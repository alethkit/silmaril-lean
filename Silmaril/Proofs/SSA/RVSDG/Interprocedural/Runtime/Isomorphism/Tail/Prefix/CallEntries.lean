module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Prefix.Observation
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Proofs

open Runtime.Isomorphism.Proofs (prepend_related)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel}
variable {outs : Ports (Ty V S)} {a b a' b' : Activation m outs}

theorem inspect_related (respects : PrimitivesRespect m ids)
    (paired : Activation.Related m ids a b)
    (safeL : inspect m a ≠ .unsupported) (safeR : inspect m b ≠ .unsupported) :
    Outcome.Related m ids (inspect m a) (inspect m b) := by
  cases paired with
  | intro callee inputs =>
    obtain ⟨values, body⟩ := Recursive.resolve_related callee
    exact expose_related respects body _ _ (prepend_related inputs values) safeL safeR

theorem step_match_right (respects : PrimitivesRespect m ids)
    (paired : Activation.Related m ids a b) (safe : inspect m b ≠ .unsupported)
    (edge : Step m a a') :
    ∃ b', Step m b b' ∧ Activation.Related m ids a' b' := by
  have observed : inspect m a = .enter a' := edge
  have matched := inspect_related respects paired (by rw [observed]; simp) safe
  rw [observed] at matched
  generalize inspected : inspect m b = outcome at matched
  cases matched with
  | enter next => exact ⟨_, inspected, next⟩

theorem step_match_left (respects : PrimitivesRespect m ids)
    (paired : Activation.Related m ids a b) (safe : inspect m a ≠ .unsupported)
    (edge : Step m b b') :
    ∃ a', Step m a a' ∧ Activation.Related m ids a' b' := by
  have observed : inspect m b = .enter b' := edge
  have matched := inspect_related respects paired safe (by rw [observed]; simp)
  rw [observed] at matched
  generalize inspected : inspect m a = outcome at matched
  cases matched with
  | enter next => exact ⟨_, inspected, next⟩

private theorem match_stream (P : Activation m outs → Activation m outs → Prop)
    (source : Nat → Activation m outs) (steps : ∀ n, Step m (source n) (source (n + 1)))
    (target : Activation m outs) (initial : P (source 0) target)
    (simulates : ∀ {a b a'}, P a b → inspect m b ≠ .unsupported → Step m a a' →
      ∃ b', Step m b b' ∧ P a' b') (supported : SupportedFrom m target) :
    ∃ run : Nat → Activation m outs, run 0 = target ∧
      (∀ n, Step m (run n) (run (n + 1))) ∧ ∀ n, P (source n) (run n) := by
  classical
  let State (n : Nat) := { b // Relation.ReflTransGen (Step m) target b ∧ P (source n) b }
  let next (n : Nat) (b : State n) :
      {b' // Step m b.val b' ∧ P (source (n + 1)) b'} :=
    Classical.indefiniteDescription _ (simulates b.property.2 (supported _ b.property.1) (steps n))
  let run : (n : Nat) → State n :=
    Nat.rec ⟨target, .refl, initial⟩ fun n b =>
      ⟨(next n b).val, b.property.1.tail (next n b).property.1, (next n b).property.2⟩
  exact ⟨fun n => (run n).val, rfl, fun n => (next n (run n)).property.1, fun n => (run n).property.2⟩

theorem stream_match_right (respects : PrimitivesRespect m ids)
    (paired : Activation.Related m ids a b) (supported : SupportedFrom m b)
    (left : Nat → Activation m outs) (initial : left 0 = a) (edges : ∀ n, Step m (left n) (left (n + 1))) :
    ∃ right : Nat → Activation m outs, right 0 = b ∧
      (∀ n, Step m (right n) (right (n + 1))) ∧ ∀ n, Activation.Related m ids (left n) (right n) :=
  match_stream (Activation.Related m ids) left edges b (initial.symm ▸ paired) (step_match_right respects) supported

theorem stream_match_left (respects : PrimitivesRespect m ids)
    (paired : Activation.Related m ids a b) (supported : SupportedFrom m a)
    (right : Nat → Activation m outs) (initial : right 0 = b) (edges : ∀ n, Step m (right n) (right (n + 1))) :
    ∃ left : Nat → Activation m outs, left 0 = a ∧
      (∀ n, Step m (left n) (left (n + 1))) ∧ ∀ n, Activation.Related m ids (left n) (right n) :=
  match_stream (fun b a => Activation.Related m ids a b) right edges a (initial.symm ▸ paired)
    (step_match_left respects) supported

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Proofs
