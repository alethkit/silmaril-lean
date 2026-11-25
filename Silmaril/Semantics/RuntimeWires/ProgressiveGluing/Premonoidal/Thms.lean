module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CentralRecoordination.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Coherence.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OuterAssociator.Thms

public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedCap

open CategoryTheory

universe u v
variable {O : Type u} {S : Signature.{u,v} O}

/-- Fixed-contact drawing classes form a premonoidal category. The whiskerings
place an active drawing beside idle strands, and composition is collared gluing.
The structural isomorphisms are geometric recoordination drawings. -/
instance premonoidal : PremonoidalCategory (FixedCap S) where
  toMonoidalCategoryStruct := geometricMonoidalData S
  tensorHom_def _ _ := by rfl
  whiskerLeft_id X Y := by exact (ActiveStrip.right.whisker X).map_id Y
  whiskerLeft_comp X {_ _ _} f g := by exact (ActiveStrip.right.whisker X).map_comp f g
  id_whiskerRight X Y := by exact (ActiveStrip.left.whisker Y).map_id X
  comp_whiskerRight f g W := by exact (ActiveStrip.left.whisker W).map_comp f g
  associator_central := by exact objectAssociator_central
  leftUnitor_central := by exact leftUnitor_central
  rightUnitor_central := by exact rightUnitor_central
  associator_naturality_left f Z W := by exact (leftAssociator Z W).hom.naturality f
  associator_naturality_middle X {_ _} f W := by exact (middleAssociator X W).hom.naturality f
  associator_naturality_right X Y {_ _} f := by exact (rightAssociator X Y).hom.naturality f
  leftUnitor_naturality f := by exact ActiveStrip.right.emptyWhiskerIso.inv.naturality f
  rightUnitor_naturality f := by exact ActiveStrip.left.emptyWhiskerIso.inv.naturality f
  pentagon W X Y Z := by exact (FixedCap.pentagon W X Y Z).symm
  triangle := by exact FixedCap.triangle

end Silmaril.RuntimeWires.ProgressiveGraph.FixedCap
