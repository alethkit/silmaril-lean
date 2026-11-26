module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Domain.Interpretation.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GeneratedDomainInterpretation

/-! # Uniqueness of interpretations on the generated domain -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Generation.Domain

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits

universe u v w x

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  {C : Type w} [CategoryTheory.Category.{x} C] [PremonoidalCategory C]
  [HasFiniteCoproducts C] [Iteration C] {X : τ → C} {T : Coordinates X}
  {instruction : ∀ p : Φ, X (instrSrc p) ⟶ X (instrTrg p)}
  (I K : Interpretation Seed T instruction)

/-- Every domain arrow has the same interpretation in the specified type coordinates. -/
theorem Interpretation.map_eq {A B : τ} (f : ofType Seed A ⟶ ofType Seed B) :
    mapInCoordinates Seed I.functor I.objIso f = mapInCoordinates Seed K.functor K.objIso f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GeneratedDomainInterpretation.map_eq Seed I K f

/-- The specified type isomorphisms give a unique natural comparison on the generated domain. -/
theorem Interpretation.comparison_existsUnique :
    ∃! e : I.functor ≅ K.functor, ∀ A : τ,
      e.hom.app (ofType Seed A) = (I.objIso A ≪≫ (K.objIso A).symm).hom :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GeneratedDomainInterpretation.comparison_existsUnique Seed I K

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Generation.Domain
