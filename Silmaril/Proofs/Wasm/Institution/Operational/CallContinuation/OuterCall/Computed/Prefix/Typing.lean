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

theorem checkOp_result {locals stack next : List Value} {op : Op}
    (step : Reduce locals stack op (.values next)) :
    checkOp (locals.map Value.type) (stackTypes stack) op = some (stackTypes next) := by
  cases step with
  | get found =>
    simp [checkOp, stackTypes, List.reverse_append, List.getElem?_map, found]
  | bin =>
    simp [checkOp, stackTypes, List.reverse_append, Value.int]

theorem preserve {locals stack next : List Value} {op : Op} {rest : List Op} {result : List NumType}
    (step : Reduce locals stack op (.values next)) (typed : WellTyped locals stack (op :: rest) result) :
    WellTyped locals next rest result := by
  simpa [WellTyped, check, checkOp_result step] using typed

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

private theorem binary_reduction {locals stack : List Value} {kind : IntType} {op : IntBinOp} {out : Outcome}
    (move : Reduce locals stack (.bin kind op) out) :
    ∃ saved x y, stack = saved ++ [Value.int kind x, Value.int kind y] ∧
      out = match Numerics.intBinOp kind op x y with
        | .ok result => .values (saved ++ [Value.int kind result])
        | .error _ => .trap saved := by
  cases move with
  | bin ok => exact ⟨_, _, _, rfl, by rw [ok]⟩
  | trap err => exact ⟨_, _, _, rfl, by rw [err]⟩

theorem reduce_unique {locals stack : List Value} {op : Op} {a b : Outcome}
    (left : Reduce locals stack op a) (right : Reduce locals stack op b) : a = b := by
  cases op with
  | get i =>
    cases left with
    | get found =>
      cases right with
      | get alsoFound =>
        cases Option.some.inj (found.symm.trans alsoFound)
        rfl
  | bin kind op =>
    obtain ⟨first, x, y, stackEq, rfl⟩ := binary_reduction left
    obtain ⟨second, x', y', stackEq', rfl⟩ := binary_reduction right
    have eq := congrArg List.reverse (stackEq.symm.trans stackEq')
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.cons.injEq] at eq
    obtain ⟨rightEq, leftEq, prefixEq⟩ := eq
    have sameRight : y = y' := eq_of_heq (Value.mk.inj rightEq).2
    have sameLeft : x = x' := eq_of_heq (Value.mk.inj leftEq).2
    rw [sameLeft, sameRight, List.reverse_inj.mp prefixEq]

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Proofs
