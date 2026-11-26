module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.NormalizationCongruence

/-! # Normalization from native rewrite classes to the continuation category -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Branch normalization preserves native rewrite equivalence at any exact
input and exit contexts. -/
theorem SubstitutionEquiv.bindBranchArguments {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : SubstitutionEquiv Γ r s L) : SubstitutionEquiv Γ r.bindBranchArguments s.bindBranchArguments L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.substitutionEquiv_normalize h

variable {Γ : VCtx τ} {L K : LCtx τ}

/-- Normalize any exactly typed continuation class to an arrow in the
continuation category. Equivalent representatives give the same arrow. -/
@[expose] def TypedContinuationClass.normalize (f : TypedContinuationClass (Φ := Φ) Γ L K) :
    ContinuationHom (Φ := Φ) Γ L K :=
  Quotient.map (fun σ : TypedContinuationFamily (Φ := Φ) Γ L K => ContinuationFamily.ofTyped σ.property)
    (fun _ _ h _ _ hi => (h hi).bindBranchArguments) f

@[simp] theorem TypedContinuationClass.normalize_mk (σ : TypedContinuationFamily (Φ := Φ) Γ L K) :
    TypedContinuationClass.normalize (Quotient.mk (typedContinuationSetoid Γ L K) σ) =
      Quotient.mk (continuationSetoid Γ L K) (ContinuationFamily.ofTyped σ.property) :=
  rfl

/-- The categorical arrows are a retract of the classes of exactly typed
families under inclusion and branch normalization. -/
@[simp] theorem ContinuationHom.normalize_toTypedClass (f : ContinuationHom (Φ := Φ) Γ L K) :
    TypedContinuationClass.normalize f.toTypedClass = f := by
  refine Quotient.inductionOn f (fun σ => ?_)
  exact ContinuationFamily.ofTyped_toHom (X := ⟨L⟩) (Y := ⟨K⟩) σ

end Silmaril.Isotope.LambdaSSA.Region
