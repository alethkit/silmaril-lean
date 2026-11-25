module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Unit.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs

/-! # Unit projection coherence and the unit η boundary -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalUnit
open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory Paper.TypeCategory
open Paper (Eqv)
open CfgEta.TypeCategory (productFstBranches productSndBranches seqValueBranches
  whiskerLeftRegion_typed whiskerRightRegion_typed)

universe u v u₁ v₁
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)
local notation "U" => (Silmaril.unit : τ)
local infixr:70 " ×ₜ " => product

set_option allowUnsafeReducibility true in
attribute [local reducible] tensorObj

private theorem leftSection_typed (A : τ) :
    ValueBranches [A] (.br 0 (.pair (.unit : Tm Φ) (.var 0))) [U ×ₜ A] :=
  .br rfl (.pair .unit (.var rfl))

private theorem rightSection_typed (A : τ) :
    ValueBranches [A] (.br 0 (.pair (.var 0) (.unit : Tm Φ))) [A ×ₜ U] :=
  .br rfl (.pair (.var rfl) .unit)

set_option backward.isDefEq.respectTransparency false in
theorem leftUnit_section_projection (A : τ) :
    leftUnitSection (Φ := Φ) A ≫ leftUnitProjection A = 𝟙 (Obj A) := by
  unfold leftUnitSection
  erw [ofRegion_comp _ _ (seqValueBranches (leftSection_typed A) (productSndBranches U A)), ← ofRegion_id]
  apply (ofRegion_eq_iff _ _).2
  exact .productBeta (.let₂Beta .unit (.var (i := 0) rfl) (.br rfl (.var (i := 0) rfl)))

set_option backward.isDefEq.respectTransparency false in
theorem rightUnit_section_projection (A : τ) :
    rightUnitSection (Φ := Φ) A ≫ rightUnitProjection A = 𝟙 (Obj A) := by
  unfold rightUnitSection
  erw [ofRegion_comp _ _ (seqValueBranches (rightSection_typed A) (productFstBranches A U)), ← ofRegion_id]
  apply (ofRegion_eq_iff _ _).2
  exact .productBeta (.let₂Beta (.var (i := 0) rfl) .unit (.br rfl (.var (i := 1) rfl)))

set_option backward.isDefEq.respectTransparency false in
theorem leftUnit_projection_section (A : τ) :
    leftUnitProjection (Φ := Φ) A ≫ leftUnitSection A =
      whiskerRight (discardArrow U) (Obj A) := by
  unfold discardArrow
  rw [whiskerRight_ofRegion]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem rightUnit_projection_section (A : τ) :
    rightUnitProjection (Φ := Φ) A ≫ rightUnitSection A =
      whiskerLeft (Obj A) (discardArrow U) := by
  unfold discardArrow
  rw [whiskerLeft_ofRegion]
  rfl


set_option backward.isDefEq.respectTransparency false in
theorem map_discard_unit_eq_id_of_mono_leftUnit
    {C : Type u₁} [Category.{v₁} C] (F : Paper.TypeCategory (τ := τ) Φ ⥤ C)
    [Mono (F.map (leftUnitProjection U))] :
    F.map (discardArrow U) = 𝟙 (F.obj (Obj U)) := by
  have section_law : F.map (leftUnitSection U) ≫ F.map (leftUnitProjection U) = 𝟙 _ := by
    rw [← F.map_comp, leftUnit_section_projection, F.map_id]
  have section_other : F.map (leftUnitProjection U) ≫ F.map (leftUnitSection U) = 𝟙 _ := by
    apply (cancel_mono (F.map (leftUnitProjection U))).mp
    rw [Category.assoc, section_law, Category.comp_id, Category.id_comp]
  have h : F.map (whiskerRight (discardArrow U) (Obj U)) = 𝟙 _ := by
    rw [← leftUnit_projection_section, F.map_comp, section_other]
  have e := congrArg (fun k => F.map k) (whiskerRight_productFst U (discardArrow (Φ := Φ) U))
  change F.map (_ ≫ rightUnitProjection U) = F.map (rightUnitProjection U ≫ discardArrow U) at e
  rw [F.map_comp, F.map_comp, h, Category.id_comp] at e
  have ep := congrArg (F.map (rightUnitSection U) ≫ ·) e
  rw [← Category.assoc, ← F.map_comp, rightUnit_section_projection, F.map_id, Category.id_comp] at ep
  exact ep.symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalUnit
