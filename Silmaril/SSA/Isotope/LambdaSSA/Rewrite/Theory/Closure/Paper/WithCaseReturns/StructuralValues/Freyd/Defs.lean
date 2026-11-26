module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Products.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

/-! # Chosen structures for the structural value inclusion -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Seed" => JoinedStep (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Val" => ValueCategory (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Comp" => TypeCategory (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "inc" => inclusion (τ := τ) (Φ := Φ) pe
local notation "unitStep" => includeUnit pe

/-- Cartesian products use the exact syntax product, and the unit uses unit η. -/
noncomputable abbrev valueCartesian : CartesianMonoidalCategory Val :=
  Extension.Singleton.StructuralValues.cartesian Seed unitStep

attribute [local instance] valueCartesian

/-- The value symmetry is induced by the Cartesian tensor. -/
noncomputable abbrev valueBraided : BraidedCategory Val :=
  BraidedCategory.ofCartesianMonoidalCategory

/-- Computations use the existing syntactic whiskers and unit-η coherence. -/
abbrev computationPremonoidal : PremonoidalCategory Comp :=
  Extension.Singleton.premonoidalOfUnitEta Seed unitStep

abbrev computationSymmetric : @SymmetricPremonoidalCategory Comp _ (computationPremonoidal pe) :=
  Extension.Singleton.symmetricPremonoidalOfUnitEta Seed unitStep

instance valueHasFiniteCoproducts : HasFiniteCoproducts Val :=
  Extension.Singleton.StructuralValues.hasFiniteCoproducts Seed

instance : PreservesFiniteCoproducts (inc) :=
  Extension.Singleton.StructuralValues.preservesFiniteCoproducts Seed

/-- Types are interpreted by their guarded syntax objects. -/
@[instance_reducible] noncomputable def typeModel : TypeModel τ Val where
  obj := ofSyntaxType pe
  productIso _ _ := Iso.refl _
  unitIso := Iso.refl _
  coprodIso A B :=
    (Extension.Singleton.StructuralValues.sumIsColimit Seed A B).coconePointUniqueUpToIso
      (colimit.isColimit _)
  emptyIsInitial := Extension.Singleton.StructuralValues.emptyIsInitial Seed

/-- Primitive instructions have their direct guarded computation representatives. -/
@[instance_reducible] def instructions : InstructionModel (inc) (typeModel pe) Φ where
  denote p := (projection pe).map (Paper.TypeCategory.primitiveReturn p)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues
