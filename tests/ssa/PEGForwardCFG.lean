module

import Silmaril.SSA.PEG.Bridge.ForwardCFG.Thms

namespace Silmaril.SSA.PEG.Bridge.ForwardCFG.Tests

open RVSDG (Tuple)
open Silmaril.SSA.LambdaRTL (upd)
open Silmaril.SSA.RVSDG.MLIR

private abbrev num : Ty Unit := .data ()

private inductive Instr : InstructionSet.{0,0} Unit
  | two : Instr [] num
  | add : Instr [num, num] num
  | sub : Instr [num, num] num

private def values : TotalModel Instr where
  carrier _ := Nat
  run
    | .two, .nil => (2 : Nat)
    | .add, .cons x (.cons y .nil) => Nat.add x y
    | .sub, .cons x (.cons y .nil) => Nat.sub x y

private abbrev params : List (Ty Unit) := [.bool, num]
private abbrev results : List (Ty Unit) := [num, num, num, .bool]
private def sorts (i : Fin 6) : Ty Unit := if i.val = 0 then .bool else num

private def graph : Graph Instr params results 6 0 where
  forest := ⟨Fin.elim0⟩
  sort := sorts
  node
    | ⟨0, _⟩ => .ofLabel (.param .head) .nil
    | ⟨1, _⟩ => .ofLabel (.param (.tail .head)) .nil
    | ⟨2, _⟩ => .ofLabel (.op .two) .nil
    | ⟨3, _⟩ => .ofLabel (.op .add) (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ .nil))
    | ⟨4, _⟩ => .ofLabel (.op .sub) (.cons ⟨3, rfl⟩ (.cons ⟨2, rfl⟩ .nil))
    | ⟨5, _⟩ => .ofLabel .phi (.cons ⟨0, rfl⟩ (.cons ⟨4, rfl⟩ (.cons ⟨1, rfl⟩ .nil)))
    | ⟨i + 6, h⟩ => False.elim (by omega)
  roots := .cons ⟨5, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨5, rfl⟩ (.cons ⟨0, rfl⟩ .nil)))

private theorem ordered : Ordered graph := by decide

private def env (flag : Bool) : Tuple values.toPEG.Value params :=
  .cons ⟨flag⟩ (.cons (5 : Nat) .nil)

private def expected (answer : Nat) (flag : Bool) : Tuple values.toPEG.Value results :=
  .cons answer (.cons (5 : Nat) (.cons answer (.cons ⟨flag⟩ .nil)))

private def entry (flag : Bool) : Store values :=
  upd (inputStore values (env flag)) (.temp 25) (.atom num (99 : Nat))

private theorem entry_inputs (flag : Bool) : Inputs values (env flag) (entry flag) := by
  intro _ p
  have different : Register.arg (ForwardCFG.Compiler.portIndex p) ≠ .temp 25 := by
    intro h
    cases h
  exact (ite_eq_right (t := Value.atom num (99 : Nat)) different).trans
    (inputStore_inputs values (env flag) p)

example : observeCFG graph ordered values (entry true) = some (Sum.inl (), expected 8 true) := rfl
example : observeCFG graph ordered values (entry false) = some (Sum.inl (), expected 5 false) := rfl

example : (toLambdaRTL graph ordered).evalSSA (model values) (entry true) =
    some ((), Value.pack (expected 8 true)) := rfl

-- Observe the written temporary, the untouched argument, and an unallocated register.
example : ((toCFG graph ordered).run (model values) (entry true)).map
    (fun (label, _, store) => (label, store (.temp 4), store (.arg 1), store (.temp 25))) =
    some (Sum.inl (), .atom num (8 : Nat), .atom num (5 : Nat), .atom num (99 : Nat)) := rfl

example : ∃ final : Store values,
    (toCFG graph ordered).run (model values) (entry false) =
      some (Sum.inl (), Value.pack (expected 5 false), final) ∧
    final (.temp 25) = entry false (.temp 25) := by
  obtain ⟨final, run, frame⟩ := cfg_run values graph ordered (env false) (entry false) (entry_inputs false)
  exact ⟨final, run, frame _ (by change (6 : Nat) ≤ 25; decide)⟩

example : (toCFG graph ordered).blocks = [] := cfg_blocks graph ordered

example : graph.observe values.toPEG
    (graph.denote values.toPEG (env true) ordered.demandWellFounded) Fin.elim0 =
    (expected 8 true).map (fun _ => some) := by
  have h := observeCFG_peg values graph ordered (env true) (entry true) (entry_inputs true)
    Fin.elim0 ordered.demandWellFounded
  exact (congrArg Prod.snd (Option.some.inj h)).symm

example :
    fromPorts results (Regionless.ofAssignment (F := values.toRVSDG.Val) results (fun i =>
      (translateMLIR graph ordered i).denote values.toMLIR
        (Regionless.toAssignment params (toPorts (F := values.toRVSDG.Val) (env true))))) =
      expected 8 true := by
  have h := observeCFG_mlir values graph ordered (env true) (entry true) (entry_inputs true)
  rw [show observeCFG graph ordered values (entry true) = some (Sum.inl (), expected 8 true)
    from rfl] at h
  exact (congrArg Prod.snd (Option.some.inj h)).symm

-- A mismatched tag fails in the λRTL model before it can be used as a natural number.
example : observeCFG graph ordered values
    (upd (entry true) (.arg 1) (.atom .bool ⟨false⟩)) = none := rfl

end Silmaril.SSA.PEG.Bridge.ForwardCFG.Tests
