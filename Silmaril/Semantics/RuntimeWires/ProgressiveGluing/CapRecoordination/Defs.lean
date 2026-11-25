module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.FixedCapCategory.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.Types

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedCap

open CategoryTheory

universe u v
variable {O : Type u} {S : Signature.{u,v} O}

/-- The ordered word of boundary types. -/
def types (a : FixedCap S) : List O := List.ofFn a.profile.label

variable {a b : FixedCap S}

/-- Match slots in order when the two cap words agree. -/
def recoordinationSlots (h : a.types = b.types) : Fin a.profile.size ≃o Fin b.profile.size :=
  Fin.castOrderIso (by exact Proofs.CapRecoordination.same_size h)

theorem recoordination_label (h : a.types = b.types) (i : Fin a.profile.size) :
    a.profile.label i = b.profile.label (recoordinationSlots h i) :=
  Proofs.CapRecoordination.same_label h i

/-- The affine collar from one cap profile to another with the same word. -/
def interpolationSpec (h : a.types = b.types) : CollarSpec O a.profile.size where
  label := a.profile.label
  bottom := a.profile.x
  top i := b.profile.x (recoordinationSlots h i)
  bottom_inside := a.inside
  top_inside i := b.inside (recoordinationSlots h i)
  bottom_injective := a.profile.ordered.injective
  order _ _ := a.profile.ordered.lt_iff_lt.trans
    ((b.profile.ordered.comp (recoordinationSlots h).strictMono).lt_iff_lt).symm

/-- A generator-free polygonal drawing with one straight interpolating
strand per ordered typed slot. -/
def interpolationDrawing (h : a.types = b.types) : FixedDrawing S a.profile b.profile where
  vertices := 0
  wires := a.profile.size
  drawing := (interpolationSpec h).drawing S
  input := (Equiv.subtypeUnivEquiv ((interpolationSpec h).drawing_start (S := S))).symm
  output := (recoordinationSlots h).symm.toEquiv.trans
    (Equiv.subtypeUnivEquiv ((interpolationSpec h).drawing_finish (S := S))).symm
  input_label := (interpolationSpec h).drawing_label
  output_label i :=
    ((interpolationSpec h).drawing_label ((recoordinationSlots h).symm i)).trans
      ((recoordination_label h _).trans (congrArg b.profile.label ((recoordinationSlots h).apply_symm_apply i)))
  input_x := (interpolationSpec h).drawing_bottom
  output_x i :=
    ((interpolationSpec h).drawing_top ((recoordinationSlots h).symm i)).trans
      (congrArg b.profile.x ((recoordinationSlots h).apply_symm_apply i))

/-- The existing geometric class of the straight interpolation. -/
def recoordinate (h : a.types = b.types) : a ⟶ b :=
  ofDrawing (interpolationDrawing h)

end Silmaril.RuntimeWires.ProgressiveGraph.FixedCap
