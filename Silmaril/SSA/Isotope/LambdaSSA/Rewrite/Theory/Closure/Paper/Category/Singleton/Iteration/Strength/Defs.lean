module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Retained.Defs

/-! # The retained-sum distributor for singleton iteration -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open CfgEta.TypeCategory.Retained (distributorRegion_typed)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory (τ := τ) Φ

/-- Move a retained factor inside the chosen coproduct using the literal typed distributor. -/
@[expose] noncomputable def leftCoproductDistributor (Z X Y : Comp) :
    tensorObj Z (X ⨿ Y) ⟶ tensorObj Z X ⨿ tensorObj Z Y :=
  let z : τ := Z
  let x : τ := X
  let y : τ := Y
  whiskerLeft Z (sumIso x y).inv ≫
    ofRegion (τ := τ) (distributorRegion_typed z x y) ≫
      (sumIso (Silmaril.product z x) (Silmaril.product z y)).hom

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
