module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Projection.Defs

/-! # Two feedback modes of the hidden-bit product -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues.HiddenBit

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open scoped MonoidalCategory

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase.Chosen (projectedChosenDistributor)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)
local notation "Seed" => Paper.WithCaseReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Q" => Paper.WithCaseReturns.TypeCategory (τ := τ) (Φ := Φ) pe
local notation "U" => (Silmaril.unit : τ)
local notation "Bit" => Silmaril.coprod U U
local notation "Obj" => ofType Seed

/-- Identify the hidden-bit product with a chosen coproduct of two visible states. -/
noncomputable def modes (A : τ) : Obj A ⨿ Obj A ≅ Obj (product A Bit) :=
  let unitIso := rightUnitIsoOfEta Seed
    (unit_eta_of_include Seed (Paper.WithCaseReturns.includeUnit pe)) (Obj A)
  coprod.mapIso unitIso.symm unitIso.symm ≪≫
    projectedChosenDistributor Seed A U U ≪≫
    (whiskerLeftFunctor Seed (Obj A)).mapIso (sumIso Seed U U).symm

/-- Select the left tag without changing the visible state. -/
noncomputable abbrev leftMode (A : τ) : Obj A ⟶ Obj (product A Bit) :=
  coprod.inl ≫ (modes pe A).hom

/-- Select the right tag without changing the visible state. -/
noncomputable abbrev rightMode (A : τ) : Obj A ⟶ Obj (product A Bit) :=
  coprod.inr ≫ (modes pe A).hom

/-- Express a hidden-bit step as a copair with a separate recursive label for each tag. -/
noncomputable abbrev rows (A : τ) {B : Q}
    (f : Obj (product A Bit) ⟶ B ⨿ Obj (product A Bit)) :
    Obj A ⨿ Obj A ⟶ (B ⨿ Obj A) ⨿ Obj A :=
  (modes pe A).hom ≫ f ≫ coprod.map (𝟙 B) (modes pe A).inv ≫
    (coprod.associator B (Obj A) (Obj A)).inv

/-- Run a visible step in either summand and switch summands on recurrence. -/
noncomputable abbrev alternatingStep {A B : Q} (g : A ⟶ B ⨿ A) : A ⨿ A ⟶ B ⨿ (A ⨿ A) :=
  coprod.desc (g ≫ coprod.map (𝟙 B) (coprod.inr : A ⟶ A ⨿ A))
    (g ≫ coprod.map (𝟙 B) (coprod.inl : A ⟶ A ⨿ A))

/-- Execute the visible step and enter the opposite mode on every repeat. -/
noncomputable abbrev flipStep (A : τ) {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    Obj (product A Bit) ⟶ B ⨿ Obj (product A Bit) :=
  (modes pe A).inv ≫ alternatingStep pe g ≫ coprod.map (𝟙 B) (modes pe A).hom

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues.HiddenBit
