module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Unit.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalUnit

/-! # Exact unit projection and section equations -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open CfgEta.TypeCategory (productFstBranches productSndBranches)

universe u v u₁ v₁
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)
local notation "U" => (Silmaril.unit : τ)
local infixr:70 " ×ₜ " => product

/-- The literal unit insertion is a section of the left projection. -/
theorem leftUnit_section_projection (A : τ) :
    leftUnitSection (Φ := Φ) A ≫ leftUnitProjection A = 𝟙 (Obj A) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalUnit.leftUnit_section_projection A

/-- The literal unit insertion is a section of the right projection. -/
theorem rightUnit_section_projection (A : τ) :
    rightUnitSection (Φ := Φ) A ≫ rightUnitProjection A = 𝟙 (Obj A) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalUnit.rightUnit_section_projection A

/-- The other left composite replaces the unit factor by literal unit. -/
theorem leftUnit_projection_section (A : τ) :
    leftUnitProjection (Φ := Φ) A ≫ leftUnitSection A = whiskerRight (discardArrow U) (Obj A) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalUnit.leftUnit_projection_section A

/-- The other right composite replaces the unit factor by literal unit. -/
theorem rightUnit_projection_section (A : τ) :
    rightUnitProjection (Φ := Φ) A ≫ rightUnitSection A = whiskerLeft (Obj A) (discardArrow U) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalUnit.rightUnit_projection_section A

/-- Monicity of the projected left unitor at unit forces unit η in the image. -/
theorem map_discard_unit_eq_id_of_mono_leftUnit
    {C : Type u₁} [Category.{v₁} C] (F : Paper.TypeCategory (τ := τ) Φ ⥤ C)
    [Mono (F.map (leftUnitProjection U))] :
    F.map (discardArrow U) = 𝟙 (F.obj (Obj U)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalUnit.map_discard_unit_eq_id_of_mono_leftUnit F

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
