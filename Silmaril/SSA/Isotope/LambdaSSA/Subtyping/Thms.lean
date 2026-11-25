module

public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Subtyping.Typing

/-! # Exact λSSA typing embeds into proof-relevant typing -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Subtyping.Exact

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ]
  {Φ : Type v} [HasTy Φ τ]

/-- Every exact expression typing admits a derivation in the subtyping calculus. -/
theorem tm {Γ : VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    (h : LambdaSSA.Tm.HasType Γ t A) : Nonempty (Tm.HasType Γ t A) :=
  tm_proof h

/-- Every exact region typing admits a derivation in the subtyping calculus. -/
theorem region {Γ : VCtx τ} {r : LambdaSSA.Region Φ} {L : LCtx τ}
    (h : LambdaSSA.Region.HasType Γ r L) : Nonempty (Region.HasType Γ r L) :=
  region_proof h

end Silmaril.Isotope.LambdaSSA.Subtyping.Exact
