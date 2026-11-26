module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDenotationPreservation

/-! # Model structure on the denotation of a sound singleton quotient -/

public section

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

/-- The quotient lift preserves guarded feedback at the exact sum type. -/
theorem denoteFunctor_map_iterateSum {A B : τ} (f : ofType Seed A ⟶ ofType Seed (coprod B A)) :
    (F).map (iterateSum Seed f) = CategoryTheory.iterate ((F).map f ≫ ((T).sumIso B A).hom) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDenotationPreservation.map_iterate J M shared sound f

/-- The sound seed supplies descent. Preservation of the generation operations
follows from the ordinary guarded interpretation at the same type coordinates. -/
theorem denoteFunctor_preserves : Preserves Seed (F) (exactObj) (T) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDenotationPreservation.preserves J M shared sound

/-- A projected typed primitive denotes the primitive supplied by the model. -/
theorem denoteFunctor_map_primitive (p : Φ) :
    mapInCoordinates Seed (F) (exactObj) (primitive Seed p) =
      InstructionModel.denote (J := J) (M := M) p :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDenotationPreservation.map_primitive J M shared sound p

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
