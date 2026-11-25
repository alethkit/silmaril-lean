module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Feedback.Thms

/-! # Continuations that preserve a prefix of exits -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}
  {X Y Z : ContinuationContext Φ Γ}

/-- Keep the first exits and lift replacements for the remaining exits past them. -/
@[expose] def prependFamily (X : ContinuationContext Φ Γ)
    (σ : ContinuationFamily (Φ := Φ) Γ Y.labels Z.labels) :
    ContinuationFamily (Φ := Φ) Γ (X.append Y).labels (X.append Z).labels :=
  ⟨liftLSubstN X.labels.length σ.val, σ.property.append X.labels⟩

end Silmaril.Isotope.LambdaSSA.Region.CfgEta
