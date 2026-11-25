module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Composition.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.NormalizationSubstitution

/-! # Composition agrees with the category after normalization -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L K P : LCtx τ}

theorem normalize_compAfterBinding
    (f : TypedContinuationClass (Φ := Φ) Γ L K) (g : TypedContinuationClass (Φ := Φ) Γ K P) :
    TypedContinuationClass.normalize (f.compAfterBinding g) =
      (TypedContinuationClass.normalize f).compose (TypedContinuationClass.normalize g) := by
  induction f, g using Quotient.inductionOn₂ with
  | _ σ υ =>
      apply Quotient.sound
      intro ℓ A hi
      change SubstitutionEquiv (A :: Γ)
        (((σ.val ℓ).bindBranchArguments.lsubst (liftLSubstVars υ.val)).bindBranchArguments)
        ((σ.val ℓ).bindBranchArguments.lsubst (liftLSubstVars (fun i => (υ.val i).bindBranchArguments))) P
      have h := normalize_lsubst_valueBranches ((σ.property hi).bindBranchArguments)
        (υ.property.liftVars A)
      simpa only [normalizeLiftVars] using h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
