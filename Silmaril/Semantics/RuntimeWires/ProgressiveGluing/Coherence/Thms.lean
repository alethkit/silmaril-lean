module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Coherence.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Coherence.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OuterAssociator.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OuterAssociator.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Coherence.Laws

public noncomputable section

/-!
# Objectwise triangle and pentagon for fixed caps

The associator and unit morphisms are the coordinate changes from the
existing natural isomorphisms. A whiskered coordinate change is compared
geometrically with the direct interpolation of its placed caps. The
comparison fixes the outer caps and matches the ordered full wire
traces. The recoordination cocycle then identifies the actual collared
composites along both paths of each law in the fixed-contact category.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedCap

open CategoryTheory

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : FixedCap S}

/-- The left-slot functors present the same component at their object actions. -/
theorem objectAssociator_left_app (A B C : FixedCap S) :
    HEq (objectAssociator A B C) ((leftAssociator B C).app A) := by rfl

/-- The right-slot functors present the same component at their object actions. -/
theorem objectAssociator_right_app (A B C : FixedCap S) :
    HEq (objectAssociator A B C) ((rightAssociator A B).app C) := by rfl

theorem objectAssociator_hom (A B C : FixedCap S) :
    (objectAssociator A B C).hom = recoordinate (objectAssociator_types A B C) :=
  Proofs.Coherence.objectAssociator_hom A B C

theorem leftUnitor_hom (A : FixedCap S) :
    (leftUnitor A).hom = recoordinate (leftUnitor_types A) :=
  Proofs.Coherence.leftUnitor_hom A

theorem rightUnitor_hom (A : FixedCap S) :
    (rightUnitor A).hom = recoordinate (rightUnitor_types A) :=
  Proofs.Coherence.rightUnitor_hom A

theorem whiskerLeft_recoordinate (idle : FixedCap S) (h : a.types = b.types) :
    whiskerLeftHom idle (recoordinate h) = recoordinate (whiskerLeft_types idle h) :=
  Proofs.Coherence.whiskerLeft_recoordinate idle h

theorem whiskerRight_recoordinate (idle : FixedCap S) (h : a.types = b.types) :
    whiskerRightHom idle (recoordinate h) = recoordinate (whiskerRight_types idle h) :=
  Proofs.Coherence.whiskerRight_recoordinate idle h

/-- The objectwise triangle with the actual empty-cap unit components. -/
theorem triangle (A B : FixedCap S) :
    (objectAssociator A (empty S) B).hom ≫ whiskerLeftHom A (leftUnitor B).hom =
      whiskerRightHom B (rightUnitor A).hom :=
  Proofs.Coherence.triangle A B

/-- The objectwise pentagon for the actual half-strip associator components. -/
theorem pentagon (A B C D : FixedCap S) :
    (objectAssociator (A.beside B) C D).hom ≫ (objectAssociator A B (C.beside D)).hom =
      whiskerRightHom D (objectAssociator A B C).hom ≫
        (objectAssociator A (B.beside C) D).hom ≫
        whiskerLeftHom A (objectAssociator B C D).hom :=
  Proofs.Coherence.pentagon A B C D

end Silmaril.RuntimeWires.ProgressiveGraph.FixedCap
