module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Drawing
import Mathlib.Data.List.OfFn

public noncomputable section

/-!
# Horizontal placement beside idle strands

The active drawing is affinely compressed into either open half of the
square. The other half contains one straight strand per idle cap slot.
Wire IDs are allocated in active-then-idle order, while the cap profiles
and enumerations use horizontal order.

The half-strip convention is a concrete placement of representatives.
Iterating it gives different coordinates for the two parenthesizations,
and the empty neighbor still rescales the nonempty cap. Any future
coherence result needs a coordinate comparison or a different placement
convention. This construction concerns horizontal juxtaposition in
Lemma 3.4 and Figure 7 of Román and Sobociński, arXiv:2305.06075v5.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O}

namespace FixedCap

/-- Concatenate types and place their coordinates in open half strips. -/
def beside (left right : FixedCap S) : FixedCap S :=
  Proofs.HorizontalPlacement.beside left right

theorem beside_labels (left right : FixedCap S) :
    List.ofFn (left.beside right).profile.label =
      List.ofFn left.profile.label ++ List.ofFn right.profile.label :=
  List.ofFn_fin_append _ _

theorem beside_size (left right : FixedCap S) :
    (left.beside right).profile.size = left.profile.size + right.profile.size := by rfl

end FixedCap

namespace ActiveStrip

variable (side : ActiveStrip)

/-- The resulting cap, with the active and idle profiles in geometric order. -/
def adjoin (active idle : FixedCap S) : FixedCap S :=
  Proofs.HorizontalPlacement.adjoin side active idle

theorem adjoin_labels (active idle : FixedCap S) :
    List.ofFn (side.adjoin active idle).profile.label =
      match side with
      | .left => List.ofFn active.profile.label ++ List.ofFn idle.profile.label
      | .right => List.ofFn idle.profile.label ++ List.ofFn active.profile.label := by
  cases side
  · exact FixedCap.beside_labels active idle
  · exact FixedCap.beside_labels idle active

/-- Identify the operand and its original slot at each concatenated cap slot. -/
def capSlots (active idle : FixedCap S) :
    Fin (side.adjoin active idle).profile.size ≃ Fin active.profile.size ⊕ Fin idle.profile.size :=
  Proofs.HorizontalPlacement.slots side active idle

theorem active_slot_x (a idle : FixedCap S) (i : Fin a.profile.size) :
    (side.adjoin a idle).profile.x ((side.capSlots a idle).symm (.inl i)) = side.place (a.profile.x i) :=
  Proofs.HorizontalPlacement.active_slot_x side a idle i

theorem idle_slot_x (a idle : FixedCap S) (i : Fin idle.profile.size) :
    (side.adjoin a idle).profile.x ((side.capSlots a idle).symm (.inr i)) = side.opposite.place (idle.profile.x i) :=
  Proofs.HorizontalPlacement.idle_slot_x side a idle i

theorem active_slot_val (a idle : FixedCap S) (i : Fin a.profile.size) :
    ((side.capSlots a idle).symm (.inl i)).val =
      match side with | .left => i.val | .right => idle.profile.size + i.val := by
  cases side <;> rfl

theorem idle_slot_val (a idle : FixedCap S) (i : Fin idle.profile.size) :
    ((side.capSlots a idle).symm (.inr i)).val =
      match side with | .left => a.profile.size + i.val | .right => i.val := by
  cases side <;> rfl

variable {a b : FixedCap S}

/-- Place an actual active diagram in this strip, with straight idle
strands in the opposite strip. -/
def placeDrawing (p : FixedDrawing S a.profile b.profile) (idle : FixedCap S) :
    FixedDrawing S (side.adjoin a idle).profile (side.adjoin b idle).profile :=
  Proofs.HorizontalPlacement.placed side idle p

variable (p : FixedDrawing S a.profile b.profile) (idle : FixedCap S)

/-- Wire indices keep the active block first in either orientation. -/
def activeWire : Fin p.wires ↪ Fin (side.placeDrawing p idle).wires :=
  Fin.castAddEmb idle.profile.size

/-- Each idle cap slot supplies a separate wire in the opposite strip. -/
def idleWire : Fin idle.profile.size ↪ Fin (side.placeDrawing p idle).wires :=
  Fin.natAddEmb p.wires

theorem wire_count : (side.placeDrawing p idle).wires = p.wires + idle.profile.size := by rfl

theorem activeWire_val (i : Fin p.wires) : (side.activeWire p idle i).val = i.val := by rfl

theorem idleWire_val (j : Fin idle.profile.size) : (side.idleWire p idle j).val = p.wires + j.val := by rfl

theorem active_label (i : Fin p.wires) :
    (side.placeDrawing p idle).drawing.label (side.activeWire p idle i) = p.drawing.label i :=
  congrArg Proofs.HorizontalPlacement.LocatedWire.label
    (Proofs.HorizontalPlacement.wire_data_active side p.drawing idle i)

theorem idle_label (j : Fin idle.profile.size) :
    (side.placeDrawing p idle).drawing.label (side.idleWire p idle j) = idle.profile.label j :=
  congrArg Proofs.HorizontalPlacement.LocatedWire.label
    (Proofs.HorizontalPlacement.wire_data_idle side p.drawing idle j)

theorem active_x (i : Fin p.wires) (y : ℝ) :
    (side.placeDrawing p idle).drawing.x (side.activeWire p idle i) y =
      side.place (p.drawing.x i y) :=
  Proofs.HorizontalPlacement.wire_x_active side p.drawing idle i y

theorem idle_x (j : Fin idle.profile.size) (y : ℝ) :
    (side.placeDrawing p idle).drawing.x (side.idleWire p idle j) y =
      side.opposite.place (idle.profile.x j) :=
  Proofs.HorizontalPlacement.wire_x_idle side p.drawing idle j y

/-- Active generator occurrences keep their indices. -/
def vertexIndex : Fin p.vertices ≃ Fin (side.placeDrawing p idle).vertices := by
  exact Equiv.refl _

theorem active_endpoints (i : Fin p.wires) :
    (side.placeDrawing p idle).drawing.start (side.activeWire p idle i) =
      (p.drawing.start i).map (side.vertexIndex p idle) ∧
    (side.placeDrawing p idle).drawing.finish (side.activeWire p idle i) =
      (p.drawing.finish i).map (side.vertexIndex p idle) := by
  exact ⟨(Proofs.HorizontalPlacement.start_active side p.drawing idle i).trans Option.map_id_apply'.symm,
    (Proofs.HorizontalPlacement.finish_active side p.drawing idle i).trans Option.map_id_apply'.symm⟩

theorem idle_endpoints (j : Fin idle.profile.size) :
    (side.placeDrawing p idle).drawing.start (side.idleWire p idle j) = none ∧
    (side.placeDrawing p idle).drawing.finish (side.idleWire p idle j) = none :=
  ⟨Proofs.HorizontalPlacement.start_idle side p.drawing idle j,
    Proofs.HorizontalPlacement.finish_idle side p.drawing idle j⟩

theorem input_active (i : Fin a.profile.size) :
    ((side.placeDrawing p idle).input ((side.capSlots a idle).symm (.inl i))).val =
      side.activeWire p idle (p.input i).val :=
  Proofs.HorizontalPlacement.contacts_active _ _ p.input i

theorem input_idle (i : Fin idle.profile.size) :
    ((side.placeDrawing p idle).input ((side.capSlots a idle).symm (.inr i))).val =
      side.idleWire p idle i :=
  Proofs.HorizontalPlacement.contacts_idle _ _ p.input i

theorem output_active (i : Fin b.profile.size) :
    ((side.placeDrawing p idle).output ((side.capSlots b idle).symm (.inl i))).val =
      side.activeWire p idle (p.output i).val :=
  Proofs.HorizontalPlacement.contacts_active _ _ p.output i

theorem output_idle (i : Fin idle.profile.size) :
    ((side.placeDrawing p idle).output ((side.capSlots b idle).symm (.inr i))).val =
      side.idleWire p idle i :=
  Proofs.HorizontalPlacement.contacts_idle _ _ p.output i

theorem input_ports (v : Fin p.vertices) :
    (side.placeDrawing p idle).drawing.inputs (side.vertexIndex p idle v) =
      (p.drawing.inputs v).map (side.activeWire p idle) := by
  rw [ProgressiveGraph.Diagram.inputs, ProgressiveGraph.Diagram.inputs, List.map_ofFn]
  rfl

theorem output_ports (v : Fin p.vertices) :
    (side.placeDrawing p idle).drawing.outputs (side.vertexIndex p idle v) =
      (p.drawing.outputs v).map (side.activeWire p idle) := by
  rw [ProgressiveGraph.Diagram.outputs, ProgressiveGraph.Diagram.outputs, List.map_ofFn]
  rfl

end ActiveStrip
end Silmaril.RuntimeWires.ProgressiveGraph
