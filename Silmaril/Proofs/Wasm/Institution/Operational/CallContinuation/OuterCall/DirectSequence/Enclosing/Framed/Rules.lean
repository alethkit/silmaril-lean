module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Proofs

open Silmaril.Semantics.SOS
open StraightLine

inductive Move (ctx : Context) (p : Program) : State ctx p.site → State ctx p.site → Prop where
  | body {a b} (step : Enclosing.Edge ctx p a b) : Move ctx p (.label a) (.label b)
  | ground {a b} (step : Ground ctx p.site a b) : Move ctx p a b

theorem invert {ctx : Context} {p : Program} {a b : State ctx p.site} (edge : Edge ctx p a b) : Move ctx p a b := by
  refine Derives.least (M := fun j => match j with
    | .body j => (Enclosing.presentation ctx p).Derives j
    | .step a b => Move ctx p a b) edge ?_
  intro r rule ih
  change RuleInstance ctx p r at rule
  cases rule with
  | inherit rule => exact Derives.apply rule (fun j mem => ih (.body j) (List.mem_map_of_mem mem))
  | underLabel a b => exact .body (ih _ (List.Mem.head _))
  | ground rule => exact .ground rule

theorem underLabel {ctx : Context} {p : Program} {a b : Enclosing.State ctx p.site}
    (step : Enclosing.Edge ctx p a b) : Edge ctx p (.label a) (.label b) := by
  have inherited := Derives.map
    (R := (Enclosing.presentation ctx p).rules) (Q := (presentation ctx p).rules)
    Judgment.body (fun _ rule => RuleInstance.inherit rule) step
  exact Derives.apply (R := (presentation ctx p).rules)
    (r := ⟨[.body (.step a b)], .step (.label a) (.label b)⟩) (.underLabel a b)
    (fun _ mem => (List.mem_singleton.mp mem).symm ▸ inherited)

theorem label_run {ctx : Context} {p : Program} {a b : Enclosing.State ctx p.site}
    (run : Enclosing.Runs ctx p a b) : Runs ctx p (.label a) (.label b) :=
  Relation.ReflTransGen.lift State.label (fun _ _ step => underLabel step) _ _ run

theorem closed {ctx : Context} {p : Program} (typed : ctx.Typed p) (program : DirectSequence.Typed p)
    (targets : p.site.body.TypedTargets) (suffix : ctx.sequence.TypedTargets) {a b : State ctx p.site}
    (ready : Admitted a) (step : Edge ctx p a b) : Admitted b := by
  cases invert step with
  | body move => exact Enclosing.closed typed program targets suffix ready move
  | ground move =>
    cases move with
    | leaveLabel finished => exact Sequence.finished_typed finished ready
    | leaveFrame => exact ready

theorem trap_unwinds {ctx : Context} {p : Program} {a b : State ctx p.site}
    (trap : Unwinding ctx p.site a) (run : Runs ctx p a b) : Unwinding ctx p.site b := by
  induction run with
  | refl => exact trap
  | tail _ edge ih =>
    cases ih with
    | label trapped =>
      cases invert edge with
      | body move => exact .label (Enclosing.trap_bypasses trapped (Relation.ReflTransGen.single move))
      | ground move =>
        cases move with
        | leaveLabel finished =>
          cases trapped with
          | trapped => cases finished; exact .exit
    | exit => cases invert edge with | ground move => cases move; exact .done
    | done => cases invert edge with | ground move => cases move

theorem run_iff {C : Type} {ctx : Context} {p : Program} (emit : State ctx p.site → C)
    (native : C → C → Prop) (typed : ctx.Typed p) (program : DirectSequence.Typed p)
    (targets : p.site.body.TypedTargets) (suffix : ctx.sequence.TypedTargets)
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

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Proofs
