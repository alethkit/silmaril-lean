module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CategoricalLink

/-! # Initiality from an empty-typed constructor value -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory.CartesianMonoidalCategory (fst lift)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- An empty-typed constructor value makes the entire input object initial
in the computation category. The value map provides a section of the first
projection from the product with the empty object. -/
theorem emptyValue_hom_ext {Γ : VCtx τ} {a : Tm Φ} (ha : Tm.BranchValue Γ a Silmaril.empty)
    {D : C} {f g : J.obj (ctxObj M Γ) ⟶ D} : f = g := by
  obtain ⟨p, _⟩ := ha.denotes_map J M
  let X := ctxObj M Γ
  let E := M.obj (Silmaril.empty : τ)
  let sectionMap : X ⟶ X ⊗ E := lift (𝟙 X) p
  have hE : (coprod.inl : E ⟶ E ⨿ E) = coprod.inr := M.emptyIsInitial.hom_ext _ _
  have h : J.map (fst X E) ≫ f = J.map (fst X E) ≫ g :=
    context_of_empty_hom_ext J hE
  have hp : sectionMap ≫ fst X E = 𝟙 X := by simp [sectionMap]
  simpa only [← Category.assoc, ← J.map_comp, hp, J.map_id, Category.id_comp] using
    congrArg (J.map sectionMap ≫ ·) h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
