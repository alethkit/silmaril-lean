module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Preservation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Domain.Interpretation.Thms

/-! # The generated interpretation of a sound singleton quotient -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

open Generation

variable {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
  (sound : SeedDenotes (Seed := Seed) J M)

set_option hygiene false in
local notation "F" => denoteFunctor J M shared sound
set_option hygiene false in
local notation "T" => Coordinates.ofModel J M
set_option hygiene false in
local notation "exactObj" => (fun A : τ => Iso.refl (J.obj (M.obj A)))

local notation "instruction" => InstructionModel.denote (J := J) (M := M)
local notation "Interpretation" => Domain.Interpretation Seed (T) (instruction)

/-- Interpret the generated domain of any sound contextual singleton quotient. -/
noncomputable def generatedInterpretation : Interpretation :=
  Domain.Interpretation.restrict Seed (F) (exactObj) (denoteFunctor_preserves J M shared sound)
    (denoteFunctor_map_primitive J M shared sound)

local notation "canonical" => generatedInterpretation J M shared sound

set_option backward.isDefEq.respectTransparency false in
/-- The comparison is pointwise on arrows of the generated domain. -/
theorem generatedInterpretation_map_eq (G : Interpretation) {A B : τ}
    (f : Domain.ofType Seed A ⟶ Domain.ofType Seed B) :
    (canonical).functor.map f = Domain.mapInCoordinates Seed G.functor G.objIso f := by
  have h := Domain.Interpretation.map_eq Seed (canonical) G f
  change 𝟙 _ ≫ (canonical).functor.map f ≫ 𝟙 _ = _ at h
  rwa [Category.comp_id, Category.id_comp] at h

set_option backward.isDefEq.respectTransparency false in
/-- The given type isomorphisms determine the unique comparison from the
canonical model to a preserving interpretation on the same domain. -/
theorem generatedInterpretation_universal (G : Interpretation) :
    ∃! e : (canonical).functor ≅ G.functor, ∀ A : τ,
      e.hom.app (Domain.ofType Seed A) = (G.objIso A).inv := by
  have coordinates (A : τ) : ((canonical).objIso A ≪≫ (G.objIso A).symm).hom = (G.objIso A).inv :=
    Category.id_comp _
  simpa only [coordinates] using Domain.Interpretation.comparison_existsUnique Seed (canonical) G

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
