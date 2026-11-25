module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OuterAssociator.Thms
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Coherence.Recoordination
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Thms

public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedCap

open CategoryTheory

universe u v
variable {O : Type u} {S : Signature.{u,v} O}

/-- The actual associator component on the ordered triple of fixed caps. -/
def objectAssociator (A B C : FixedCap S) : ((A.beside B).beside C) ≅ (A.beside (B.beside C)) := by
  exact (middleAssociator A C).app B

/-- Remove the empty left half strip using the corresponding unit component. -/
def leftUnitor (A : FixedCap S) : (empty S).beside A ≅ A := by
  exact ((ActiveStrip.right.emptyWhiskerIso (S := S)).app A).symm

/-- Remove the empty right half strip using the corresponding unit component. -/
def rightUnitor (A : FixedCap S) : A.beside (empty S) ≅ A := by
  exact ((ActiveStrip.left.emptyWhiskerIso (S := S)).app A).symm

theorem objectAssociator_types (A B C : FixedCap S) :
    ((A.beside B).beside C).types = (A.beside (B.beside C)).types := by
  exact middleAssociator_types A B C

theorem leftUnitor_types (A : FixedCap S) : ((empty S).beside A).types = A.types := by
  exact (ActiveStrip.right.empty_types A).symm

theorem rightUnitor_types (A : FixedCap S) : (A.beside (empty S)).types = A.types := by
  exact (ActiveStrip.left.empty_types A).symm

variable {a b : FixedCap S}

/-- Whisker a morphism with an idle left cap. -/
def whiskerLeftHom (idle : FixedCap S) (f : a ⟶ b) : idle.beside a ⟶ idle.beside b := by
  exact (ActiveStrip.right.whisker idle).map f

/-- Whisker a morphism with an idle right cap. -/
def whiskerRightHom (idle : FixedCap S) (f : a ⟶ b) : a.beside idle ⟶ b.beside idle := by
  exact (ActiveStrip.left.whisker idle).map f

theorem whiskerLeft_types (idle : FixedCap S) (h : a.types = b.types) :
    (idle.beside a).types = (idle.beside b).types := by
  exact ActiveStrip.right.whisker_types idle h

theorem whiskerRight_types (idle : FixedCap S) (h : a.types = b.types) :
    (a.beside idle).types = (b.beside idle).types := by
  exact ActiveStrip.left.whisker_types idle h

end Silmaril.RuntimeWires.ProgressiveGraph.FixedCap
