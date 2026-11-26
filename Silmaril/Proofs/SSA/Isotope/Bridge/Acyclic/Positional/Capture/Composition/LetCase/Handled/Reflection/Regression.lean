module

import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Fixture

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory Silmaril.Elgot.ITree
open Region (packedExitType)
open Isotope.Semantics (BoundEnv)
open LetCase.Structural.Finite (Context Shape StructuralContext Types)
open LetCase.Structural.Reply (Γ₀)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase (HandledTrace.Program HandledTrace.Arrow)
open LetIter.PaperExpression.Source.FreeTree.Response (Structured.toSmall Structured.Event)
open LetSeq.StraightLine.Structural (Log)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

local notation "Value" => LetCase.Structural.Finite.Value

/-! ## A separating history -/

/-- The history is shown by exactly one of the two packed programs. -/
example : HasTrace ((pack captures (Case.seq route route)).run (model Op) start) (history repeated finish) ∧
    ¬ HasTrace ((pack captures (Case.seq route echo)).run (model Op) start) (history repeated finish) := by
  rw [run_twice, run_crossed]
  exact ⟨twice_shows, crossed_hides⟩

/-! ## Policies that replay the history separate the arrows -/

example : Replay (scripted Op) repeated (history repeated finish) := scripted_replay repeated finish

example : (handledFunctor (model Op) (scripted Op) input).map both ≠
    (handledFunctor (model Op) (scripted Op) input).map mixed :=
  fun same => native_differ ((scripted_map_eq_iff input both mixed).mp same)

example : (handledFunctor (model Op) (permissive Op) input).map both ≠
    (handledFunctor (model Op) (permissive Op) input).map mixed :=
  fun same => native_differ ((permissive_map_eq_iff input both mixed).mp same)

/-- The separation at the scripted policy, on representatives: started at
the listed history, one direction of handled-trace inclusion fails. -/
example : ¬ HandledTraceLE (scripted Op) repeated
    ((pack captures (Case.seq route route)).run (model Op) start)
    ((pack captures (Case.seq route echo)).run (model Op) start) := by
  rw [run_twice, run_crossed]
  exact fun included => crossed_hides (included _ ⟨twice_shows, scripted_replay repeated finish⟩).1

example : (handledFunctor (model Op) (scripted Op) input).Faithful ∧
    (ssaHandledFunctor (model Op) (scripted Op) input).Faithful :=
  ⟨handledFunctor_faithful input _ scripted_exposes, ssaHandledFunctor_faithful input _ scripted_exposes⟩

/-! ## The alternating policy identifies them

The reply is the current state and each exchange flips the state. This
policy never repeats a reply, so it cannot replay the separating history. -/

private def replyBit : (f : Op) → Value (instrTrg f) → Bool
  | .ask, .inl _ => false
  | .ask, .inr _ => true

private def alternating : Handler Bool (Events Op)
  | ⟨_, .call f _⟩, state, reply, next => replyBit f reply = state ∧ next = !state

example (state : Bool) : ¬ Replay alternating state (history repeated finish) := by
  rintro ⟨_, first, _, second, -⟩
  have flipped : state = !state := by
    rw [first.2] at second
    exact first.1.symm.trans second.1
  cases state <;> cases flipped

/-- The premise of the reflection theorem fails for this policy. -/
example : ¬ Exposes alternating := fun exposes => by
  obtain ⟨state, _, first, _, second, -⟩ := exposes repeated finish
  have flipped : state = !state := by
    rw [first.2] at second
    exact first.1.symm.trans second.1
  cases state <;> cases flipped

private theorem alternating_vis {R : Type} (e : Events Op R) {k l : R → Tree (Events Op) Packed} (state : Bool)
    (admitted : ∀ reply next, alternating ⟨R, e⟩ state reply next →
      HandledTraceLE alternating next (k reply) (l reply)) :
    HandledTraceLE alternating state (vis e k) (vis e l) := by
  rintro trace ⟨seen, replay⟩
  cases trace with
  | «prefix» => exact ⟨trivial, trivial⟩
  | request d => exact ⟨(hasTrace_vis_request_iff e l d).mpr ((hasTrace_vis_request_iff e k d).mp seen), trivial⟩
  | result value =>
    have returned : out (vis e k) = Part.some (.ret value) := seen
    rw [out_vis] at returned
    cases Part.some_injective returned
  | exchange d reply tail =>
    obtain ⟨sameType, sameEvent, inner⟩ := (hasTrace_vis_exchange e k d reply tail).mp seen
    subst sameType
    subst sameEvent
    obtain ⟨next, step, rest⟩ := replay
    have below := admitted reply next step tail ⟨inner, rest⟩
    exact ⟨(hasTrace_vis_exchange_iff d l reply tail).mpr below.1, next, step, below.2⟩

private theorem opposite {first second : Value Bit} {state : Bool}
    (one : replyBit Op.ask first = state) (two : replyBit Op.ask second = !state) :
    packet second = other (packet first) := by
  subst one
  rcases first with _ | _ <;> rcases second with _ | _ <;> first | rfl | cases two

private theorem alternating_collapses (state : Bool) (capture : Val Bit) (x : Val Packet) :
    HandledTraceLE alternating state (twice capture x) (crossed capture x) ∧
      HandledTraceLE alternating state (crossed capture x) (twice capture x) := by
  constructor <;>
  · refine alternating_vis _ state fun first next step => ?_
    obtain ⟨one, rfl⟩ := step
    refine alternating_vis _ _ fun second _ step => ?_
    rw [opposite one step.1]

example : (handledFunctor (model Op) alternating input).map both =
    (handledFunctor (model Op) alternating input).map mixed :=
  Quotient.sound
    ⟨fun w state => by rw [run_twice, run_crossed]; exact (alternating_collapses state w.1 w.2).1,
      fun w state => by rw [run_twice, run_crossed]; exact (alternating_collapses state w.1 w.2).2⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
