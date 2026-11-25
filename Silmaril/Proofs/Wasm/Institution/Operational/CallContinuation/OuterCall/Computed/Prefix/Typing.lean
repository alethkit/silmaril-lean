module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Proofs

open Execution.Runtime (Value)

theorem check_append (locals stack : List NumType) (before after : List Op) :
    check locals stack (before ++ after) =
      (check locals stack before).bind fun next => check locals next after := by
  induction before generalizing stack with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.cons_append, check]
    cases checkOp locals stack op with
    | none => rfl
    | some next => exact ih next

theorem nil_iff {locals stack : List Value} {result : List NumType} :
    WellTyped locals stack [] result ↔ stack.map Value.type = result := by
  simp [WellTyped, check, stackTypes]

theorem preserve {locals stack next : List Value} {op : Op} {rest : List Op} {result : List NumType}
    (step : Reduce locals stack op (.values next)) (typed : WellTyped locals stack (op :: rest) result) :
    WellTyped locals next rest result := by
  cases step with
  | get found =>
    simpa [WellTyped, check, checkOp, stackTypes, List.reverse_append, List.getElem?_map, found] using typed
  | bin =>
    simpa [WellTyped, check, checkOp, stackTypes, List.reverse_append, Value.int] using typed

theorem progress {locals stack : List Value} {op : Op} {tail : List Op} {result : List NumType}
    (typed : WellTyped locals stack (op :: tail) result) : ∃ out, Reduce locals stack op out := by
  cases op with
  | get i =>
    cases lookup : locals[i.toNat]? with
    | none => simp [WellTyped, check, checkOp, List.getElem?_map, lookup] at typed
    | some v => exact ⟨_, .get lookup⟩
  | bin t oper =>
    cases reverse : stack.reverse with
    | nil => simp [WellTyped, check, checkOp, stackTypes, ← List.map_reverse, reverse] at typed
    | cons right rest =>
      cases rest with
      | nil => simp [WellTyped, check, checkOp, stackTypes, ← List.map_reverse, reverse] at typed
      | cons left saved =>
        have types : left.type = .int t ∧ right.type = .int t := by
          by_contra bad
          simp [WellTyped, check, checkOp, stackTypes, ← List.map_reverse, reverse, bad] at typed
        have stackEq := congrArg List.reverse reverse
        simp only [List.reverse_reverse, List.reverse_cons, List.append_assoc, List.singleton_append] at stackEq
        rcases left with ⟨lt, x⟩
        rcases right with ⟨rt, y⟩
        obtain ⟨rfl, rfl⟩ := types
        subst stack
        cases ans : Numerics.intBinOp t oper x y with
        | ok z => exact ⟨_, .bin ans⟩
        | error cause => exact ⟨_, .trap ans⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Proofs
