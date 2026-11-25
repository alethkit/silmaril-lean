module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Naturality.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.CategoryNaturality

/-! # Naturality of singleton iteration in the CFG η quotient -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}
  {A B C : τ}

/-- The sum's return injection is the second exit of the feedback interface. -/
@[reassoc]
theorem iterationDispatch_inl (A B : τ) :
    (sumCofan (Φ := Φ) (Γ := Γ) B A).inl.hom ≫ fromNative.map
      (SyntacticCategory.iterationDispatchHom A B) =
        fromNative.map ((ContinuationContext.single A).appendInr (ContinuationContext.single B)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.dispatch_inl A B

/-- The sum's repeat injection is the first exit of the feedback interface. -/
@[reassoc]
theorem iterationDispatch_inr (A B : τ) :
    (sumCofan (Φ := Φ) (Γ := Γ) B A).inr.hom ≫ fromNative.map
      (SyntacticCategory.iterationDispatchHom A B) =
        fromNative.map ((ContinuationContext.single A).appendInl (ContinuationContext.single B)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.dispatch_inr A B

/-- The exact-sum form of companion `Eqv.fixpoint_seq`, with no extra exits. -/
theorem iterateSum_naturality
    (f : ofType (Φ := Φ) (Γ := Γ) A ⟶ ofType (Silmaril.coprod B A))
    (g : ofType (Φ := Φ) (Γ := Γ) B ⟶ ofType C) :
    iterateSum f ≫ g = iterateSum (f ≫ mapReturn A g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.iterateSum_naturality f g

/-- Postcomposition acts on the return summand of an arbitrary iteration step. -/
theorem iterate_naturality {X Y Z : TypeCategory Φ Γ} (f : X ⟶ Y ⨿ X) (g : Y ⟶ Z) :
    iterate f ≫ g = iterate (f ≫ coprod.map g (𝟙 X)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.iterate_naturality f g

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
