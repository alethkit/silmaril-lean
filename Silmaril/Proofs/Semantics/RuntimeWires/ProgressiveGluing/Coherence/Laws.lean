module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Coherence.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Coherence.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Thms

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.Coherence

open ProgressiveGraph CategoryTheory FixedCap

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : FixedCap S}

theorem objectAssociator_hom (A B C : FixedCap S) :
    (objectAssociator A B C).hom = recoordinate (objectAssociator_types A B C) := by rfl

theorem leftUnitor_hom (A : FixedCap S) :
    (leftUnitor A).hom = recoordinate (leftUnitor_types A) := by rfl

theorem rightUnitor_hom (A : FixedCap S) :
    (rightUnitor A).hom = recoordinate (rightUnitor_types A) := by rfl

theorem whiskerLeft_recoordinate (idle : FixedCap S) (h : a.types = b.types) :
    whiskerLeftHom idle (recoordinate h) = recoordinate (whiskerLeft_types idle h) := by
  exact ActiveStrip.right.whisker_recoordinate idle h

theorem whiskerRight_recoordinate (idle : FixedCap S) (h : a.types = b.types) :
    whiskerRightHom idle (recoordinate h) = recoordinate (whiskerRight_types idle h) := by
  exact ActiveStrip.left.whisker_recoordinate idle h

theorem triangle (A B : FixedCap S) :
    (objectAssociator A (empty S) B).hom ≫ whiskerLeftHom A (leftUnitor B).hom =
      whiskerRightHom B (rightUnitor A).hom := by
  simp only [objectAssociator_hom, leftUnitor_hom, rightUnitor_hom,
    whiskerLeft_recoordinate, whiskerRight_recoordinate, recoordinate_comp]

theorem pentagon (A B C D : FixedCap S) :
    (objectAssociator (A.beside B) C D).hom ≫ (objectAssociator A B (C.beside D)).hom =
      whiskerRightHom D (objectAssociator A B C).hom ≫
        (objectAssociator A (B.beside C) D).hom ≫
        whiskerLeftHom A (objectAssociator B C D).hom := by
  simp only [objectAssociator_hom, whiskerLeft_recoordinate, whiskerRight_recoordinate, recoordinate_comp]

end Silmaril.RuntimeWires.Proofs.Coherence
