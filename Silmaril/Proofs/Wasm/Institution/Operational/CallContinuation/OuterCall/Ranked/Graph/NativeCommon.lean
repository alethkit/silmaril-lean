module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs

open Execution.Runtime (FuncAddr Frame Value)
open Computed

theorem split_call {fn : Function} {stack : List Value} {target : CallTarget} {rest : List Op}
    (typed : fn.WellTyped stack (.call target :: rest)) :
    ∃ saved operands, stack = saved ++ operands ∧ target ∈ fn.targets ∧
      operands.length = target.declaration.params.length := by
  unfold Function.WellTyped at typed
  simp only [checkCode, Bool.and_eq_true_iff, decide_eq_true_eq] at typed
  obtain ⟨⟨used, shape⟩, _⟩ := typed
  have length : min target.declaration.params.length stack.length = target.declaration.params.length := by
    simpa [Prefix.stackTypes] using congrArg List.length shape
  have enough : target.declaration.params.length ≤ stack.length := by omega
  let below := stack.length - target.declaration.params.length
  exact ⟨stack.take below, stack.drop below, (List.take_append_drop below stack).symm, used,
    by simp [below]; omega⟩

theorem result_length {fn : Function} {values : List Value} (typed : fn.ResultTyped (.values values)) :
    values.length = fn.declaration.results.length :=
  (List.length_map ..).symm.trans (congrArg List.length typed)

theorem render_attach {A : Type} {ops : Syntax A}
    (append : ∀ xs ys, ops.values (xs ++ ys) = ops.values xs ++ ops.values ys)
    (saved : List Value) (target : CallTarget) (rest : List Op) (child : Phase) :
    (Body.attach saved target rest child).render ops =
      ops.values saved ++ child.render ops target ++ rest.map ops.emit := by
  cases child with
  | done result => cases result <;> simp [Body.attach, Body.render, Phase.render, Nested.resultCode, append]
  | _ => rfl

theorem run_iff {C : Type} {program : Program} {checked : program.check = true}
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    (render : Phase → C) (native : C → C → Prop)
    (one : ∀ {a b}, Admitted program fn a → (native (render a) b ↔
      ∃ out, program.Edge checked address a out ∧ b = render out))
    {a : Phase} {b : C} (ready : Admitted program fn a) :
    Relation.ReflTransGen native (render a) b ↔
      ∃ out, program.Runs checked address a out ∧ Admitted program fn out ∧ b = render out := by
  constructor
  · intro run
    induction run with
    | refl => exact ⟨a, .refl, ready, rfl⟩
    | tail _ step ih =>
      obtain ⟨_, trace, admitted, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := (one admitted).mp step
      exact ⟨out, trace.tail edge, program.admitted_step checked found admitted edge, rfl⟩
  · rintro ⟨out, run, readyOut, rfl⟩
    clear readyOut
    induction run with
    | refl => exact .refl
    | tail trace edge ih =>
      exact ih.tail ((one (program.admitted_run checked found ready trace)).mpr ⟨_, edge, rfl⟩)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs
