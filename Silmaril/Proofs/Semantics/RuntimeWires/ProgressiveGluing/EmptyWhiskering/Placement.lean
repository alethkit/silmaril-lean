module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Ambient
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Drawing

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.EmptyWhiskering

open ProgressiveGraph
open HorizontalPlacement (start_active finish_active)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} (side : ActiveStrip) {a b : FixedCap S}

abbrev empty (S : Signature.{u,v} O) : FixedCap S := FixedCap.empty S
abbrev placedCap (a : FixedCap S) := side.adjoin a (empty S)
abbrev slot (a : FixedCap S) := (FixedCap.recoordinationSlots (side.empty_types a)).toEquiv

theorem slot_eq (a : FixedCap S) (i : Fin a.profile.size) :
    slot side a i = (side.capSlots a (empty S)).symm (.inl i) := by
  apply Fin.ext
  change i.val = _
  rw [side.active_slot_val]
  cases side
  · rfl
  · exact (Nat.zero_add i.val).symm

theorem slot_x (a : FixedCap S) (i : Fin a.profile.size) :
    (placedCap side a).profile.x (slot side a i) = side.place (a.profile.x i) := by
  rw [slot_eq]
  exact side.active_slot_x a (empty S) i

abbrev shift (a : FixedCap S) : FixedDrawing S a.profile (placedCap side a).profile :=
  FixedCap.interpolationDrawing (side.empty_types a)

theorem shift_x (a : FixedCap S) (i : Fin a.profile.size) (t : ℝ) :
    (shift side a).drawing.x i t = track side t (a.profile.x i) :=
  (FixedCap.interpolation_x (side.empty_types a) i t).trans
    (congrArg (fun x => interpolate (a.profile.x i) x t) (slot_x side a i))

theorem shift_input (a : FixedCap S) (i : Fin a.profile.size) :
    ((shift side a).input i).val = i := rfl

theorem shift_output (a : FixedCap S) (i : Fin a.profile.size) :
    ((shift side a).output (slot side a i)).val = i := by
  change (slot side a).symm (slot side a i) = i
  exact (slot side a).symm_apply_apply i

variable (p : FixedDrawing S a.profile b.profile)

abbrev placedCore := side.placeDrawing (a := a) (b := b) p (empty S)

def placedWires : Fin p.wires ≃ Fin (placedCore side p).wires :=
  finCongr (((side.wire_count (a := a) (b := b) p (empty S)).trans (Nat.add_zero p.wires)).symm)

theorem placedWires_apply (w : Fin p.wires) :
    placedWires side p w = side.activeWire p (empty S) w := by
  apply Fin.ext
  rfl

def placedIncidence : p.drawing.IncidenceEquiv (placedCore side p).drawing where
  vertex := side.vertexIndex p (empty S)
  wire := placedWires side p
  generator _ := by rfl
  label w := (congrArg (placedCore side p).drawing.label (placedWires_apply side p w)).trans
    (side.active_label p (empty S) w)
  inputs j := (side.input_ports p (empty S) j).trans
    (congrArg (fun f => (p.drawing.inputs j).map f) (funext (placedWires_apply side p)).symm)
  outputs j := (side.output_ports p (empty S) j).trans
    (congrArg (fun f => (p.drawing.outputs j).map f) (funext (placedWires_apply side p)).symm)

theorem placed_x (w : Fin p.wires) (y : ℝ) :
    (placedCore side p).drawing.x (placedWires side p w) y = side.place (p.drawing.x w y) :=
  (congrArg (fun i => (placedCore side p).drawing.x i y) (placedWires_apply side p w)).trans
    (side.active_x p (empty S) w y)

theorem placed_covers (w : Fin p.wires) (y : ℝ) :
    p.drawing.covers w y ↔ (placedCore side p).drawing.covers (placedWires side p w) y := by
  rw [placedWires_apply]
  change p.drawing.covers w y ↔ (HorizontalPlacement.drawing side p.drawing (empty S)).covers
    (Fin.castAdd (empty S).profile.size w) y
  simp only [Diagram.covers, Diagram.lower, Diagram.upper, start_active, finish_active]
  rfl

theorem placed_input (i : Fin a.profile.size) :
    ((placedCore side p).input (slot side a i)).val = placedWires side p (p.input i).val := by
  rw [slot_eq, placedWires_apply]
  exact side.input_active p (empty S) i

theorem placed_output (i : Fin b.profile.size) :
    ((placedCore side p).output (slot side b i)).val = placedWires side p (p.output i).val := by
  rw [slot_eq, placedWires_apply]
  exact side.output_active p (empty S) i

theorem placed_vertexX (j : Fin p.vertices) :
    (placedCore side p).drawing.vertexX ((placedIncidence side p).vertex j) =
      side.place (p.drawing.vertexX j) := by rfl

theorem placed_vertexHeight (j : Fin p.vertices) :
    (placedCore side p).drawing.vertexHeight ((placedIncidence side p).vertex j) =
      p.drawing.vertexHeight j := by rfl

end Silmaril.RuntimeWires.Proofs.EmptyWhiskering
