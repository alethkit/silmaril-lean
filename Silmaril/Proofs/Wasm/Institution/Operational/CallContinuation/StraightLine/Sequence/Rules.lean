module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Thms
public import Silmaril.Wasm.Institution.Operational.CallFrame.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Proofs

open Silmaril.Semantics.SOS
open Execution.Runtime (Value)
open OuterCall.Computed

inductive Move (site : Site) : State site → State site → Prop where
  | ground {a b} (rule : Ground site a b) : Move site a b
  | call {i : site.TargetId} {a b : CallFrame.State} {rest : List (Op site)}
      (live : Active a) (edge : CallFrame.Edge (site.target i).callee a b) :
      Move site (.active i a rest) (attach i rest b)

theorem invert {site : Site} {a b : State site} (edge : Edge site a b) : Move site a b := by
  refine Derives.least (M := fun j => match j with
    | .callee i j => (CallFrame.presentation (site.target i).callee).Derives j
    | .step a b => Move site a b) edge ?_
  intro r rule ih
  change RuleInstance site r at rule
  cases rule with
  | @inherit i r h => exact Derives.apply h (fun j mem => ih (.callee i j) (List.mem_map_of_mem mem))
  | call i a b rest live => exact .call live (ih _ (List.Mem.head _))
  | ground h => exact .ground h

theorem call {site : Site} {i : site.TargetId} {a b : CallFrame.State} {rest : List (Op site)}
    (live : Active a) (edge : CallFrame.Edge (site.target i).callee a b) :
    Edge site (.active i a rest) (attach i rest b) := by
  have h := Derives.map
    (R := (CallFrame.presentation (site.target i).callee).rules) (Q := (presentation site).rules)
    (Judgment.callee i) (fun _ rule => RuleInstance.inherit i rule) edge
  exact Derives.apply (R := (presentation site).rules)
    (r := ⟨[.callee i (.call a b)], .step (.active i a rest) (attach i rest b)⟩) (.call i a b rest live)
    (fun _ mem => (List.mem_singleton.mp mem).symm ▸ h)

theorem check_append (site : Site) (types : List NumType) (before after : List (Op site)) :
    check site types (before ++ after) = (check site types before).bind (fun next => check site next after) := by
  induction before generalizing types with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.cons_append, check]
    cases checkOp site types op with
    | none => rfl
    | some types => exact ih types

theorem check_numeric (site : Site) (types : List NumType) (code : List Prefix.Op) :
    check site types (code.map .numeric) = Prefix.check (site.frame.locals.map Value.type) types code := by
  induction code generalizing types with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.map_cons, check, checkOp, Prefix.check]
    cases Prefix.checkOp (site.frame.locals.map Value.type) types op with
    | none => rfl
    | some types => exact ih types

private theorem checked_call {site : Site} {stack : List Value} {i : site.TargetId} {rest : List (Op site)}
    (ready : WellTyped site stack (.call i :: rest)) :
    (Prefix.stackTypes stack).take (site.target i).callee.params.length = (site.target i).callee.params.reverse := by
  by_contra bad
  simp [WellTyped, check, checkOp, bad] at ready

theorem split {site : Site} {stack : List Value} {i : site.TargetId} {rest : List (Op site)}
    (ready : WellTyped site stack (.call i :: rest)) :
    ∃ saved args, stack = saved ++ args ∧ args.length = (site.target i).callee.params.length := by
  let count := (site.target i).callee.params.length
  have len : count ≤ stack.length := by
    have lengths := congrArg List.length (checked_call ready)
    simp [Prefix.stackTypes, List.length_take, ← show count = (site.target i).callee.params.length from rfl] at lengths
    omega
  refine ⟨(stack.reverse.drop count).reverse, (stack.reverse.take count).reverse, ?_, ?_⟩
  · rw [← List.reverse_append, List.take_append_drop, List.reverse_reverse]
  · simp [List.length_take, Nat.min_eq_left len, count]

private theorem resolved_typed {site : Site} {i : site.TargetId} {saved args : List Value} {rest : List (Op site)}
    (guard : site.TypedTargets) (ready : Admitted site (.running (saved ++ args) (.call i :: rest)))
    (count : args.length = (site.target i).callee.params.length) :
    Admitted site (.active i (.invoke saved args) rest) := by
  have types : Prefix.stackTypes (saved ++ args) = Prefix.stackTypes args ++ Prefix.stackTypes saved := by
    simp [Prefix.stackTypes, List.map_append, List.reverse_append]
  have len : (Prefix.stackTypes args).length = (site.target i).callee.params.length := by
    simpa [Prefix.stackTypes] using count
  have takes := checked_call ready
  rw [types, ← len, List.take_left] at takes
  refine ⟨trivial, ⟨by simpa [Prefix.stackTypes] using takes, guard i⟩, ?_⟩
  change check site (Prefix.stackTypes (saved ++ args)) (.call i :: rest) = some site.results.reverse at ready
  simp only [check, checkOp, types] at ready
  rw [← len, List.take_left, List.drop_left, takes, ite_eq_left rfl] at ready
  exact ready

private theorem attached_typed {site : Site} {i : site.TargetId} {a b : CallFrame.State}
    {rest : List (Op site)} (ready : Admitted site (.active i a rest))
    (edge : CallFrame.Edge (site.target i).callee a b) : Admitted site (attach i rest b) := by
  have typed := CallFrame.closed ready.2.1 edge
  have kept := CallFrame.saved_of_live edge (by
    intro saved eq
    rw [eq] at ready
    exact ready.1)
  have resume : ResumeTyped site i b.saved rest := kept.symm ▸ ready.2.2
  cases b with
  | invoke | label | exit => exact ⟨trivial, typed, resume⟩
  | trapped => trivial
  | returned saved results =>
    change (results.map Value.type).reverse = (site.target i).callee.result.toList at typed
    simpa [attach, Admitted, ResumeTyped, CallFrame.State.saved, WellTyped, Prefix.stackTypes,
      List.map_append, List.reverse_append, typed] using resume

theorem finished_typed {site : Site} {q : State site} {r : Nested.Result}
    (finished : Finished site q r) (ready : Admitted site q) : ResultTyped site r := by
  cases finished with
  | values stack =>
    change some (Prefix.stackTypes stack) = some site.results.reverse at ready
    exact List.reverse_injective (Option.some.inj ready)
  | trap => trivial

theorem result_arity {site : Site} {r : Nested.Result} (typed : ResultTyped site r) : ResultArity site r := by
  cases r with
  | values stack =>
    change stack.map Value.type = site.results at typed
    simpa [ResultArity] using congrArg List.length typed
  | trap => trivial

theorem closed {site : Site} (guard : site.TypedTargets) {a b : State site}
    (ready : Admitted site a) (edge : Edge site a b) : Admitted site b := by
  cases invert edge with
  | call _ move => exact attached_typed ready move
  | ground rule =>
    cases rule with
    | resolve _ _ _ _ count => exact resolved_typed guard ready count
    | discard => trivial
    | @numeric stack op rest out step =>
      cases out with
      | trap => trivial
      | values =>
        simpa [Admitted, afterOp, WellTyped, check, checkOp, Prefix.checkOp_result step] using ready

theorem trap_bypasses {site : Site} {stack : List Value} {rest : List (Op site)} {b : State site}
    (run : Runs site (.trapped stack rest) b) : ∃ kept remaining, b = .trapped kept remaining := by
  induction run with
  | refl => exact ⟨stack, rest, rfl⟩
  | tail _ step ih =>
    obtain ⟨_, _, rfl⟩ := ih
    cases invert step with
    | ground rule =>
      cases rule with
      | discard _ => exact ⟨_, _, rfl⟩

theorem run_iff {C : Type} {site : Site} (emit : State site → C) (native : C → C → Prop)
    (typed : site.TypedTargets)
    (sound : ∀ {a b}, Edge site a b → native (emit a) (emit b))
    (readback : ∀ {a b}, Admitted site a → native (emit a) b → ∃ out, Edge site a out ∧ b = emit out)
    {a : State site} {b : C} (ready : Admitted site a) :
    Relation.ReflTransGen native (emit a) b ↔ ∃ out, Runs site a out ∧ Admitted site out ∧ b = emit out := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨a, .refl, ready, rfl⟩
    | tail _ step ih =>
      obtain ⟨middle, path, admitted, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := readback admitted step
      exact ⟨out, path.tail edge, closed typed admitted edge, rfl⟩
  · rintro ⟨out, path, _, rfl⟩
    exact Relation.ReflTransGen.lift emit (fun _ _ e => sound e) _ _ path

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Proofs
