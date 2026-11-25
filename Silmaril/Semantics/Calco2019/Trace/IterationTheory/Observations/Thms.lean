module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Observations.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.IterationObservations

/-! # Least-fixed-point observations and comparison of ranked systems -/

public section

universe u v w z

namespace Silmaril.Calco2019.IterationTheory

open Silmaril.Semantics.Domain

variable {σ : Signature.{u}} {P : Type v} {S : Type w} {T : Type z}

/-- Least fixed points unfold to the explicit finite path observations. -/
theorem least_paths (g : System σ P S) (s : S) (p : List Nat) :
    fix (update g) s p = observe g s p :=
  Proofs.IterationObservations.least_paths g s p

/-- The pointed ω-cpo semantics separates states up to bisimulation. -/
theorem least_eq_iff_bisim (g : System σ P S) (h : System σ P T) (s : S) (t : T) :
    fix (update g) s = fix (update h) t ↔
      ∃ R : S → T → Prop, Bisimulation g h R ∧ R s t :=
  Proofs.IterationObservations.least_eq_iff_bisim g h s t

/-- Two finite systems agree at their chosen states exactly when both are
images of a common finite system, with the selected state mapped to both. -/
theorem least_eq_iff_finite_span [Finite S] [Finite T]
    (g : System σ P S) (h : System σ P T) (s : S) (t : T) :
    fix (update g) s = fix (update h) t ↔
      ∃ (Z : Type (max w z)) (_ : Finite Z) (k : System σ P Z)
        (left : Z → S) (right : Z → T) (z₀ : Z),
        PreservesEquations k g left ∧ PreservesEquations k h right ∧
          left z₀ = s ∧ right z₀ = t :=
  Proofs.IterationObservations.least_eq_iff_finite_span g h s t

end Silmaril.Calco2019.IterationTheory
