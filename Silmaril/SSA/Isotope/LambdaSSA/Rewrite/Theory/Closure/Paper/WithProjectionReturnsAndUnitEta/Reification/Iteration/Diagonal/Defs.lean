module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.BinaryProducts.Thms

/-! # Product coordinates for the value diagonal of a carried step -/

@[expose] public section

universe u v w u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (ofType DiscardPreservingValueCategory discardPreservingBinaryFanIsLimit)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification (fstMap sndMap)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := τ) (Φ := Φ)
set_option hygiene false in
local notation "Values" => DiscardPreservingValueCategory (Seed) pe
set_option hygiene false in
local notation "Val" => fun (A : τ) => (⟨ofType (Seed) A⟩ : Values)

/-- The chosen diagonal is the value product lift of the two identity maps. -/
noncomputable def chosenValueDiagonal (P : τ) : Val P ⟶ Val (product P P) :=
  BinaryFan.IsLimit.lift
    (discardPreservingBinaryFanIsLimit (Seed) pe P P (fun h => Or.inl h)) (𝟙 _) (𝟙 _)

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (K : V ⥤ Values) (M : TypeModel τ V)

/-- Normalize the product coordinate using the two interpreted packed projections. -/
noncomputable def chosenValueProductMap (P : τ) (e : K.obj (M.obj P) ≅ Val P) :
    K.obj (M.obj (product P P)) ⟶ Val (product P P) :=
  BinaryFan.IsLimit.lift (discardPreservingBinaryFanIsLimit (Seed) pe P P (fun h => Or.inl h))
    (K.map (fstMap M P P) ≫ e.hom) (K.map (sndMap M P P) ≫ e.hom)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.Reification
