module

import Silmaril.Logic.Temporal.TLA.Rules.Thms

/-! Checked examples for the standalone quantifier and refinement rules. -/

namespace Silmaril.Logic.Temporal.TLA.Rules.Examples

private def startsLow : Formula Bool := .state (· = false)

private def history : Formula (Bool × Bool) :=
  .spec (fun s => s = (false, false))
    (fun s t => t.2 = (s.2 || t.1)) id (.state fun _ => True)

private def seenHigh (σ : Behavior Bool) : Behavior Bool
  | 0 => false
  | n + 1 => seenHigh σ n || σ (n + 1)

/-- A latch recording whether the visible bit has ever been high imposes no
additional constraint on a visible run that starts low. Its value can depend
on the past when the visible bit returns to low. -/
example (σ : Behavior Bool) : hide history.Sat σ ↔ startsLow.Sat σ := by
  apply hide_extension_iff startsLow.sat_stutterInvariant
  · intro τ h
    exact congrArg Prod.fst h.1
  · intro τ h
    refine ⟨fun n => (τ n, seenHigh τ n), rfl, ?_⟩
    exact ⟨congrArg (fun b => (b, false)) h, fun _ _ => Or.inl rfl, trivial⟩

private def reverseEncoding : Formula (Bool × Nat) :=
  .spec (fun s => s = (true, 0))
    (fun s t => t.2 = if t.1 then s.2 else 1) id (.state fun _ => True)

/-- Hiding preserves the refinement that inverts the visible bit and recodes
the Boolean history with natural numbers. -/
example : General.Refines (hide history.Sat) Bool.not (hide reverseEncoding.Sat) := by
  apply hide_refines (g := fun s => if s.2 then 1 else 0)
  intro σ h
  obtain ⟨initial, steps, _⟩ := h
  refine ⟨congrArg (fun s : Bool × Bool => (!s.1, if s.2 then 1 else 0)) initial, ?_, trivial⟩
  intro n hn
  rcases steps n hn with update | stay
  · left
    change (σ (n + 1)).2 = ((σ n).2 || (σ (n + 1)).1) at update
    change (if (σ (n + 1)).2 then 1 else 0) =
      (if !(σ (n + 1)).1 then (if (σ n).2 then 1 else 0) else 1)
    rw [update]
    cases (σ (n + 1)).1 <;> simp
  · exact Or.inr (congrArg (fun s : Bool × Bool => (!s.1, if s.2 then 1 else 0)) stay)

private def changeSecond : Action (Bool × Bool) :=
  fun s t => t.1 = s.1 ∧ t.2 ≠ s.2

/-- The diagonal refinement is a Boolean instance of §8.3.3. In the target,
the angle action is enabled. Pulling back the action first makes it impossible. -/
example (z : Bool) :
    (changeSecond.angle id).enabled (z, z) ∧
      ¬ (Action.enabled fun x y : Bool => (changeSecond.angle id) (x, x) (y, y)) z := by
  constructor
  · have different : (!z) ≠ z := by cases z <;> decide
    exact ⟨(z, !z), ⟨rfl, different⟩, fun h => different (congrArg Prod.snd h)⟩
  · rintro ⟨z', ⟨same, different⟩, _⟩
    exact different same

open General

private abbrev value (_ : Unit) := Bool
private def scope : Scope Unit := ⟨fun _ => Unit, fun _ => Unit⟩

private def wire : General.Formula value (scope.bindFlex ()) :=
  .always (.state (.atom fun _ s => Valuation.last s = !s () (Context.old ())))

/-- E1 constructs a bound wire as the Boolean complement of a visible signal
at every instant, even when the visible signal changes. -/
example (ρ : RigidEnv value scope) (σ : Behavior (State value scope)) :
    (General.Formula.existsFlex () wire).Sat ρ σ := by
  apply wire.existsFlex_intro (fun _ s => !s () ()) ρ σ
  intro _
  rfl

private def observedStart : General.Formula value scope :=
  .state (.atom fun _ s => s () () = true)

/-- E2 recovers an initial-state constraint on the visible signal from a
specification that also constrains the hidden wire. -/
example :
    (General.Formula.existsFlex ()
      (.conj wire (observedStart.rename (Scope.Rename.weakenFlex scope ())))).Entails
      observedStart :=
  General.Formula.existsFlex_elim fun _ h => h.2

private def rigidCopy : General.Formula value (scope.bindRigid ()) :=
  .conj (.state (.atom fun ρ _ => Valuation.last ρ = !ρ () (Context.old ())))
    (observedStart.rename (Scope.Rename.weakenRigid scope ()))

/-- F1 computes a rigid witness from a rigid parameter. F2 recovers the
independent constraint on the initial visible signal. -/
example (ρ : RigidEnv value scope) (σ : Behavior (State value scope)) :
    (General.Formula.existsRigid () rigidCopy).Sat ρ σ ↔ observedStart.Sat ρ σ := by
  constructor
  · exact General.Formula.existsRigid_elim (p := rigidCopy) (q := observedStart)
      (fun _ h => h.2) ⟨ρ, σ⟩
  · intro h
    exact rigidCopy.existsRigid_intro (fun env => !env () ()) ρ σ ⟨rfl, h⟩

end Silmaril.Logic.Temporal.TLA.Rules.Examples
