module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Composition.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.NormalizationSubstitution
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.NormalizedComposition

/-! # Native composition under normalization -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L K P : LCtx τ}

/-- At value branches, normalizing after substitution is a native rewrite
of substituting the normalized continuation bodies. -/
theorem ValueBranches.normalize_lsubst {r : Region Φ} (hr : ValueBranches Γ r L)
    {σ : Nat → Region Φ} (hσ : LSubst.HasType Γ L K σ) :
    SubstitutionEquiv Γ (r.lsubst σ).bindBranchArguments
      (r.lsubst (fun i => (σ i).bindBranchArguments)) K :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.normalize_lsubst_valueBranches hr hσ

/-- Composing exactly typed continuations after binding the producer's
branch arguments gives categorical composition under branch normalization. -/
theorem TypedContinuationClass.normalize_compAfterBinding
    (f : TypedContinuationClass (Φ := Φ) Γ L K) (g : TypedContinuationClass (Φ := Φ) Γ K P) :
    TypedContinuationClass.normalize (f.compAfterBinding g) =
      (TypedContinuationClass.normalize f).compose (TypedContinuationClass.normalize g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.normalize_compAfterBinding f g

end Silmaril.Isotope.LambdaSSA.Region
