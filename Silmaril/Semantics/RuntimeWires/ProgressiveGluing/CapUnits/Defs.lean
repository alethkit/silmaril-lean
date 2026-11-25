module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Defs
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarGeometry

@[expose] public section

namespace Silmaril.RuntimeWires.ProgressiveGraph

universe u v
variable {O : Type u}

/-- The open-square condition on the horizontal coordinates of a cap. -/
def CapProfile.Inside (a : CapProfile O) : Prop :=
  ∀ i, a.x i ∈ Set.Ioo (0 : ℝ) 1

/-- The cap without contacts. -/
def CapProfile.empty : CapProfile O where
  size := 0
  label := Fin.elim0
  x := Fin.elim0
  ordered := fun i => i.elim0

namespace FixedDrawing

variable (S : Signature.{u,v} O) (a : CapProfile O)

/-- The affine collar whose two lists of contacts are the same. -/
def identitySpec (h : a.Inside) : CollarSpec O a.size where
  label := a.label
  bottom := a.x
  top := a.x
  bottom_inside := h
  top_inside := h
  bottom_injective := a.ordered.injective
  order _ _ := Iff.rfl

/-- The vertex-free drawing with one straight strand at each cap slot. -/
noncomputable def identity (h : a.Inside) : FixedDrawing S a a where
  vertices := 0
  wires := a.size
  drawing := (identitySpec a h).drawing S
  input := (Equiv.subtypeUnivEquiv (fun i => (identitySpec a h).drawing_start (S := S) i)).symm
  output := (Equiv.subtypeUnivEquiv (fun i => (identitySpec a h).drawing_finish (S := S) i)).symm
  input_label := (identitySpec a h).drawing_label
  output_label := (identitySpec a h).drawing_label
  input_x := (identitySpec a h).drawing_bottom
  output_x := (identitySpec a h).drawing_top

end FixedDrawing
end Silmaril.RuntimeWires.ProgressiveGraph
