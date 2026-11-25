module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.Ambient

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.CapRecoordination

open ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : CapProfile O}
variable (p q : FixedDrawing S a b) (hp : p.vertices = 0) (hq : q.vertices = 0)

def wireEquiv : Fin p.wires ≃ Fin q.wires :=
  (inputWires p hp).symm.trans (inputWires q hq)

theorem wire_at_input (i : Fin a.size) :
    wireEquiv p q hp hq (p.input i).val = (q.input i).val := by
  change (inputWires q hq) ((inputWires p hp).symm (inputWires p hp i)) = inputWires q hq i
  rw [Equiv.symm_apply_apply]

theorem trace_match (w : Fin p.wires) :
    (ambient p hp q hq).plane '' (p.drawing.wire w).trace =
      (q.drawing.wire (wireEquiv p q hp hq w)).trace := by
  obtain ⟨i, rfl⟩ := (inputWires p hp).surjective w
  change (ambient p hp q hq).plane '' (p.drawing.wire (p.input i).val).trace = _
  show _ = (q.drawing.wire (wireEquiv p q hp hq (p.input i).val)).trace
  rw [wire_at_input]
  ext z
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, (covers q hq _ y).mpr ((covers p hp _ y).mp hy),
      (ambient_point p hp q hq i ((covers p hp _ y).mp hy)).symm⟩
  · rintro ⟨y, hy, rfl⟩
    have height := (covers q hq _ y).mp hy
    exact ⟨_, ⟨y, (covers p hp _ y).mpr height, rfl⟩, ambient_point p hp q hq i height⟩

def compare : p.drawing.CapComparison q.drawing where
  map := ambient p hp q hq
  incidence :=
    { vertex := finCongr (hp.trans hq.symm)
      wire := wireEquiv p q hp hq
      generator j := (no_vertex p hp j).elim
      label w := by
        obtain ⟨i, rfl⟩ := (inputWires p hp).surjective w
        change q.drawing.label (wireEquiv p q hp hq (p.input i).val) = p.drawing.label (p.input i).val
        rw [wire_at_input, q.input_label, p.input_label]
      inputs j := (no_vertex p hp j).elim
      outputs j := (no_vertex p hp j).elim }
  trace := trace_match p q hp hq
  vertex j := (no_vertex p hp j).elim

end Silmaril.RuntimeWires.Proofs.CapRecoordination
