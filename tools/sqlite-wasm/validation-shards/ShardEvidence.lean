module

public import SqliteWasm.ReactorValidation
import SqliteWasmArtifactEntries

namespace SqliteWasm.ShardEvidence

open Silmaril.Wasm.Validation

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private def checkRange? (start width : Nat) : Option Bool :=
  (bodyInputs? sqlite).map fun inputs =>
    allPairs (defaultCheckers.func inputs.context)
      ((sqlite.funcs.drop start).take width) ((inputs.signatures.drop start).take width)

sqlite_check_eq from32 : checkRange? 32 16 = some true
sqlite_check_eq from48 : checkRange? 48 16 = some true
sqlite_check_eq from64 : checkRange? 64 8 = some true

private theorem takeSplit {α : Type} (xs : List α) (start width : Nat) :
    xs.take (start + width) = xs.take start ++ (xs.drop start).take width := by
  have keep : min start (start + width) = start := Nat.min_eq_left (Nat.le_add_right ..)
  simpa only [List.take_take, keep, List.drop_take, Nat.add_sub_cancel_left] using
    (List.take_append_drop start (xs.take (start + width))).symm

private theorem allPairsAppend {α β : Type} {p : α → β → Bool}
    {xs xs' : List α} {ys ys' : List β}
    (front : allPairs p xs ys = true) (tail : allPairs p xs' ys' = true) :
    allPairs p (xs ++ xs') (ys ++ ys') = true := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact tail
    | cons b bs => simp [allPairs] at front
  | cons a as ih =>
    cases ys with
    | nil => simp [allPairs] at front
    | cons b bs =>
      simp only [List.cons_append, allPairs, Bool.and_eq_true] at front ⊢
      exact ⟨front.1, ih front.2⟩

private theorem rangeChecked {inputs : BodyInputs} {start width : Nat}
    (prepared : bodyInputs? sqlite = some inputs) (checked : checkRange? start width = some true) :
    allPairs (defaultCheckers.func inputs.context)
      ((sqlite.funcs.drop start).take width) ((inputs.signatures.drop start).take width) = true := by
  simpa only [checkRange?, prepared, Option.map_some, Option.some.injEq] using checked

private theorem appendRanges {inputs : BodyInputs} {start left right : Nat}
    (front : allPairs (defaultCheckers.func inputs.context)
      ((sqlite.funcs.drop start).take left) ((inputs.signatures.drop start).take left) = true)
    (tail : allPairs (defaultCheckers.func inputs.context)
      ((sqlite.funcs.drop (start + left)).take right)
      ((inputs.signatures.drop (start + left)).take right) = true) :
    allPairs (defaultCheckers.func inputs.context)
      ((sqlite.funcs.drop start).take (left + right))
      ((inputs.signatures.drop start).take (left + right)) = true := by
  rw [takeSplit (sqlite.funcs.drop start) left right,
    takeSplit (inputs.signatures.drop start) left right]
  simp only [List.drop_drop]
  exact allPairsAppend front tail

public theorem additionalBodies {inputs : BodyInputs} (prepared : bodyInputs? sqlite = some inputs) :
    allPairs (defaultCheckers.func inputs.context)
      ((sqlite.funcs.drop 32).take 40) ((inputs.signatures.drop 32).take 40) = true :=
  appendRanges (rangeChecked prepared from32)
    (appendRanges (rangeChecked prepared from48) (rangeChecked prepared from64))

public theorem first72Bodies :
    ∃ inputs, bodyInputs? sqlite = some inputs ∧
      List.Forall₂ (FuncOk inputs.context) (sqlite.funcs.take 72) (inputs.signatures.take 72) := by
  obtain ⟨inputs, prepared, checked⟩ := originalFirstBodies
  refine ⟨inputs, prepared, ?_⟩
  change List.Forall₂ _ (sqlite.funcs.take (32 + 40)) (inputs.signatures.take (32 + 40))
  rw [takeSplit sqlite.funcs 32 40, takeSplit inputs.signatures 32 40]
  exact List.rel_append checked (allPairs_sound defaultCheckers_sound.func (additionalBodies prepared))

end SqliteWasm.ShardEvidence
