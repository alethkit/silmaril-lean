module

public import Silmaril.Logic.Temporal.TLA.Elaborator.Defs
import Silmaril.Logic.Temporal.TLA.Thms

public section

namespace Silmaril.Logic.Temporal.TLA.Elaborator

/-- Selecting a checked state predicate as a step uses exactly its source lift. -/
theorem CheckedModule.stepPredicate_of_statePredicate {signature : Signature}
    (checked : CheckedModule signature) (name : Surface.Ident) (p : Kernel.StatePredicate signature.scope)
    (h : checked.statePredicate name = .ok p) : checked.stepPredicate name = .ok p.current := by
  simp only [CheckedModule.statePredicate, CheckedModule.stepPredicate] at h ⊢
  generalize checked.predicate name = result at h ⊢
  rcases result with _ | (_ | _) <;> cases h <;> rfl

namespace TemporalFormula

variable {Γ : Kernel.Scope} (step : Kernel.StepPredicate Γ)
  (observe : Observation Γ) (ρ : Kernel.RigidEnv Γ) (σ : Behavior (Kernel.State Γ))

/-- A source bracket permits either the raw step or observation equality on
each adjacent pair. -/
theorem sat_alwaysBracket : ((alwaysBracket step observe).toFormula ρ).Sat σ ↔
    ∀ j, step.toAction ρ (σ j) (σ (j + 1)) ∨ observe ρ (σ (j + 1)) = observe ρ (σ j) :=
  ⟨fun h j => h j (Nat.zero_le j), fun h j _ => h j⟩

/-- Continuous enablement of visible steps from some point forces recurrent
visible steps. Enabledness ranges over the full typed state space. -/
theorem sat_weakFair : ((weakFair step observe).toFormula ρ).Sat σ ↔
    ((∃ i, ∀ j, i ≤ j → ((step.toAction ρ).angle (observe ρ)).enabled (σ j)) →
      ∀ i, ∃ j, i ≤ j ∧ (step.toAction ρ).angle (observe ρ) (σ j) (σ (j + 1))) := by
  change (Formula.weakFair (step.toAction ρ) (observe ρ)).Holds σ 0 ↔ _
  simp only [Formula.holds_weakFair, Nat.zero_le, true_and, true_implies]

/-- Recurrent enablement of visible steps forces recurrent visible steps. -/
theorem sat_strongFair : ((strongFair step observe).toFormula ρ).Sat σ ↔
    ((∀ i, ∃ j, i ≤ j ∧ ((step.toAction ρ).angle (observe ρ)).enabled (σ j)) →
      ∀ i, ∃ j, i ≤ j ∧ (step.toAction ρ).angle (observe ρ) (σ j) (σ (j + 1))) := by
  change (Formula.strongFair (step.toAction ρ) (observe ρ)).Holds σ 0 ↔ _
  simp only [Formula.holds_strongFair, Nat.zero_le, true_implies]

end TemporalFormula

end Silmaril.Logic.Temporal.TLA.Elaborator
