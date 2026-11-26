module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Denotation.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseAndUnaryReturnDenotation

/-! # Comparing return-quotient denotation on generated arrows -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseAndUnaryReturns

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

open Extension.Singleton (ofType ofRegion iterateSum)
open Extension.Singleton.Generation
open CfgEta.TypeCategory (returnRegion_typed)

set_option hygiene false in
local notation "Seed" => Step (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "F" => denoteFunctor (Φ := Φ) pe J M shared
set_option hygiene false in
local notation "T" => Coordinates.ofModel J M
set_option hygiene false in
local notation "exactObj" => (fun A : τ => Iso.refl (J.obj (M.obj A)))

/-- The lifted interpretation preserves guarded iteration on the exact
result-or-state sum used by the generation theorem. -/
theorem denoteFunctor_map_iterateSum {A B : τ}
    (f : ofType (Seed) A ⟶ ofType (Seed) (coprod B A)) :
    (F).map (iterateSum (Seed) f) =
      CategoryTheory.iterate ((F).map f ≫ ((T).sumIso B A).hom) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseAndUnaryReturnDenotation.denoteFunctor_map_iterateSum pe J M shared f

variable (G : TypeCategory (τ := τ) (Φ := Φ) pe ⥤ C)
  (objIso : ∀ A : τ, G.obj (ofType (Seed) A) ≅ J.obj (M.obj A))
  (hF : Preserves (Seed) (F) (exactObj) (T)) (hG : Preserves (Seed) G objIso (T))
  (hp : ∀ p : Φ, mapInCoordinates (Seed) (F) (exactObj) (primitive (Seed) p) =
    mapInCoordinates (Seed) G objIso (primitive (Seed) p))

/-- Compare the descended interpretation with a structure-preserving candidate
on the generated wide subcategory, in the given model coordinates. -/
noncomputable def generatedDenoteIso :
    generatedInclusion (Seed) ⋙ (F) ≅ generatedInclusion (Seed) ⋙ G :=
  generatedIso (Seed) (F) (exactObj) G objIso (T) hF hG hp

include hF hG hp in
/-- In model coordinates the candidate computes the same arrow as the ordinary
guarded denotation for each admitted case/unary returning term. -/
theorem denote_returnFragment {A B : τ} {t : Tm Φ} {ht : Tm.HasType [A] t B}
    (h : ReturnFragment pe ht) :
    denoteSingletonRegion J M (returnRegion_typed ht).hasType =
      mapInCoordinates (Seed) G objIso (ofRegion (Seed) (returnRegion_typed ht)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseAndUnaryReturnDenotation.denote_returnFragment pe J M shared G objIso hF hG hp h

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseAndUnaryReturns
