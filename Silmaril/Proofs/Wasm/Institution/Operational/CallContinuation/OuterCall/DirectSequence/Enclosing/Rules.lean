module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Proofs

open Silmaril.Semantics.SOS
open StraightLine
open Execution.Runtime (Value)

inductive Move (ctx : Context) (p : Program) : State ctx p.site → State ctx p.site → Prop where
  | invoke {a b : DirectSequence.State p.site} (live : Live a) (step : DirectSequence.Edge p a b) :
      Move ctx p (.active a) (attach ctx b)
  | resume {a b : Sequence.State ctx.sequence} (step : Sequence.Edge ctx.sequence a b) :
      Move ctx p (.continuation a) (.continuation b)

theorem invert {ctx : Context} {p : Program} {a b : State ctx p.site} (edge : Edge ctx p a b) : Move ctx p a b := by
  refine Derives.least (M := fun j => match j with
    | .invocation j => (DirectSequence.presentation p).Derives j
    | .suffix j => (Sequence.presentation ctx.sequence).Derives j
    | .step a b => Move ctx p a b) edge ?_
  intro r rule ih
  change RuleInstance ctx p r at rule
  cases rule with
  | inheritInvocation rule => exact Derives.apply rule (fun j mem => ih (.invocation j) (List.mem_map_of_mem mem))
  | inheritSuffix rule => exact Derives.apply rule (fun j mem => ih (.suffix j) (List.mem_map_of_mem mem))
  | invoke b live => exact .invoke live (ih _ (List.Mem.head _))
  | resume a b => exact .resume (ih _ (List.Mem.head _))

theorem invoke {ctx : Context} {p : Program} {a b : DirectSequence.State p.site}
    (live : Live a) (edge : DirectSequence.Edge p a b) : Edge ctx p (.active a) (attach ctx b) := by
  have inherited := Derives.map
    (R := (DirectSequence.presentation p).rules) (Q := (presentation ctx p).rules)
    Judgment.invocation (fun _ rule => RuleInstance.inheritInvocation rule) edge
  exact Derives.apply (R := (presentation ctx p).rules)
    (r := ⟨[.invocation (.step a b)], .step (.active a) (attach ctx b)⟩) (.invoke b live)
    (fun _ mem => (List.mem_singleton.mp mem).symm ▸ inherited)

theorem resume {ctx : Context} {p : Program} {a b : Sequence.State ctx.sequence}
    (step : Sequence.Edge ctx.sequence a b) : Edge ctx p (.continuation a) (.continuation b) := by
  have inherited := Derives.map
    (R := (Sequence.presentation ctx.sequence).rules) (Q := (presentation ctx p).rules)
    Judgment.suffix (fun _ rule => RuleInstance.inheritSuffix rule) step
  exact Derives.apply (R := (presentation ctx p).rules)
    (r := ⟨[.suffix (.step a b)], .step (.continuation a) (.continuation b)⟩) (.resume a b)
    (fun _ mem => (List.mem_singleton.mp mem).symm ▸ inherited)

theorem resume_run {ctx : Context} {p : Program} {a b : Sequence.State ctx.sequence}
    (run : Sequence.Runs ctx.sequence a b) : Runs ctx p (.continuation a) (.continuation b) :=
  Relation.ReflTransGen.lift State.continuation (fun _ _ step => resume step) _ _ run

theorem numeric_typed_iff {p : Program} (frame : Execution.Runtime.Frame)
    (saved : List Value) (code : List Computed.Prefix.Op) (results : List NumType) :
    (Context.numeric frame saved code results).Typed p ↔
      Computed.Prefix.check (frame.locals.map Value.type)
        (p.site.result.toList.reverse ++ Computed.Prefix.stackTypes saved) code = some results.reverse := by
  unfold Context.Typed
  exact Eq.congr_left (Sequence.check_numeric _ _ _)

theorem invoke_run {ctx : Context} {p : Program} {a b : DirectSequence.State p.site}
    (run : DirectSequence.Runs p a b) : Runs ctx p (attach ctx a) (attach ctx b) := by
  refine Relation.ReflTransGen.lift (attach ctx) ?_ _ _ run
  intro before after step
  cases before with
  | done _ => exact (DirectSequence.done_no_edge step).elim
  | _ => exact invoke trivial step

theorem attached {ctx : Context} {p : Program} (typed : ctx.Typed p) {q : DirectSequence.State p.site}
    (ready : DirectSequence.Admitted p.site q) : Admitted (attach ctx q) := by
  cases q with
  | call | invoke | label | exit => exact ⟨trivial, ready⟩
  | done result =>
    cases result with
    | trap => trivial
    | values stack =>
      change stack.map Value.type = p.site.result.toList at ready
      simpa [Context.Typed, Admitted, attach, Sequence.Admitted, Sequence.WellTyped, Computed.Prefix.stackTypes,
        List.map_append, List.reverse_append, ready] using typed

theorem closed {ctx : Context} {p : Program} (typed : ctx.Typed p) (program : DirectSequence.Typed p)
    (targets : p.site.body.TypedTargets) (suffix : ctx.sequence.TypedTargets) {a b : State ctx p.site}
    (ready : Admitted a) (edge : Edge ctx p a b) : Admitted b := by
  cases invert edge with
  | invoke _ step => exact attached typed (DirectSequence.closed program targets ready.2 step)
  | resume step => exact Sequence.closed suffix ready step

theorem trap_bypasses {ctx : Context} {p : Program} {a b : State ctx p.site}
    (trapped : Unwinding ctx p.site a) (run : Runs ctx p a b) : Unwinding ctx p.site b := by
  induction run with
  | refl => exact trapped
  | tail _ edge ih =>
    cases ih with
    | active trapped live =>
      cases invert edge with
      | invoke _ move =>
        have stillTrapped := DirectSequence.trap_bypasses trapped (Relation.ReflTransGen.single move)
        cases stillTrapped with
        | label stack rest => exact .active (.label stack rest) trivial
        | exit => exact .active .exit trivial
        | done => exact .trapped ctx.saved ctx.continuation
    | trapped stack rest =>
      cases invert edge with
      | resume move =>
        obtain ⟨kept, rest, rfl⟩ := Sequence.trap_bypasses (Relation.ReflTransGen.single move)
        exact .trapped kept rest

theorem run_iff {C : Type} {ctx : Context} {p : Program} (emit : State ctx p.site → C) (native : C → C → Prop)
    (typed : ctx.Typed p) (program : DirectSequence.Typed p) (targets : p.site.body.TypedTargets) (suffix : ctx.sequence.TypedTargets)
    (sound : ∀ {a b}, Edge ctx p a b → native (emit a) (emit b))
    (read : ∀ {a b}, Admitted a → native (emit a) b → ∃ out, Edge ctx p a out ∧ b = emit out)
    {a : State ctx p.site} {b : C} (ready : Admitted a) :
    Relation.ReflTransGen native (emit a) b ↔ ∃ out, Runs ctx p a out ∧ Admitted out ∧ b = emit out := by
  constructor
  · intro run
    induction run with
    | refl => exact ⟨a, .refl, ready, rfl⟩
    | tail _ step ih =>
      obtain ⟨mid, path, admitted, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := read admitted step
      exact ⟨out, path.tail edge, closed typed program targets suffix admitted edge, rfl⟩
  · rintro ⟨out, path, _, rfl⟩
    exact Relation.ReflTransGen.lift emit (fun _ _ edge => sound edge) _ _ path

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Proofs
