module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Comparison
import Mathlib.Order.Hom.Set

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.MiddleAssociator

open ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b a' b' : FixedCap S}

/-- A single horizontal coordinate change of the middle slab. It preserves
height and ordered incidence, while the two cap coordinates may change. -/
structure CoreTransport (g : ℝ → ℝ) (p : FixedDrawing S a.profile b.profile)
    (q : FixedDrawing S a'.profile b'.profile) where
  incidence : p.drawing.IncidenceEquiv q.drawing
  vertex_x : ∀ j, q.drawing.vertexX (incidence.vertex j) = g (p.drawing.vertexX j)
  vertex_height : ∀ j, q.drawing.vertexHeight (incidence.vertex j) = p.drawing.vertexHeight j
  wire_x : ∀ w y, p.drawing.covers w y → q.drawing.x (incidence.wire w) y = g (p.drawing.x w y)

namespace CoreTransport

variable {g : ℝ → ℝ} {p : FixedDrawing S a.profile b.profile} {q : FixedDrawing S a'.profile b'.profile}
variable (D : CoreTransport g p q)

theorem covers (w : Fin p.wires) (y : ℝ) :
    p.drawing.covers w y ↔ q.drawing.covers (D.incidence.wire w) y := by
  unfold ProgressiveGraph.Diagram.covers ProgressiveGraph.Diagram.lower ProgressiveGraph.Diagram.upper
  rw [D.incidence.start, D.incidence.finish]
  cases p.drawing.start w <;> cases p.drawing.finish w <;>
    simp [endpointHeight, D.vertex_height]

def inputIndex : Fin a.profile.size ≃ Fin a'.profile.size :=
  p.input.trans ((D.incidence.wire.subtypeEquiv fun w => by
    rw [D.incidence.start]
    cases p.drawing.start w <;> simp).trans q.input.symm)

def outputIndex : Fin b.profile.size ≃ Fin b'.profile.size :=
  p.output.trans ((D.incidence.wire.subtypeEquiv fun w => by
    rw [D.incidence.finish]
    cases p.drawing.finish w <;> simp).trans q.output.symm)

theorem input_wire (i : Fin a.profile.size) :
    (q.input (D.inputIndex i)).val = D.incidence.wire (p.input i).val := by
  simp only [inputIndex, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem output_wire (i : Fin b.profile.size) :
    (q.output (D.outputIndex i)).val = D.incidence.wire (p.output i).val := by
  simp only [outputIndex, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem input_x (i : Fin a.profile.size) : a'.profile.x (D.inputIndex i) = g (a.profile.x i) := by
  rw [← q.input_x, input_wire, D.wire_x _ _ (EmptyWhiskering.input_cover p i), p.input_x]

theorem output_x (i : Fin b.profile.size) : b'.profile.x (D.outputIndex i) = g (b.profile.x i) := by
  rw [← q.output_x, output_wire, D.wire_x _ _ (EmptyWhiskering.output_cover p i), p.output_x]

/-- Increasing bijections of the finite ordered slots agree with the
canonical slot match used by an interpolating drawing. -/
def capOrder {c d : CapProfile O} (hg : StrictMono g) (e : Fin c.size ≃ Fin d.size)
    (x : ∀ i, d.x (e i) = g (c.x i)) : Fin c.size ≃o Fin d.size where
  toEquiv := e
  map_rel_iff' {i j} := by
    rw [← d.ordered.le_iff_le, x, x, hg.le_iff_le, c.ordered.le_iff_le]

theorem input_slot (hg : StrictMono g) (h : a.types = a'.types) (i : Fin a.profile.size) :
    D.inputIndex i = FixedCap.recoordinationSlots h i :=
  congrArg (fun e : Fin a.profile.size ≃o Fin a'.profile.size => e i)
    (Subsingleton.elim (capOrder hg D.inputIndex D.input_x) (FixedCap.recoordinationSlots h))

theorem output_slot (hg : StrictMono g) (h : b.types = b'.types) (i : Fin b.profile.size) :
    D.outputIndex i = FixedCap.recoordinationSlots h i :=
  congrArg (fun e : Fin b.profile.size ≃o Fin b'.profile.size => e i)
    (Subsingleton.elim (capOrder hg D.outputIndex D.output_x) (FixedCap.recoordinationSlots h))

end CoreTransport

end Silmaril.RuntimeWires.Proofs.MiddleAssociator
