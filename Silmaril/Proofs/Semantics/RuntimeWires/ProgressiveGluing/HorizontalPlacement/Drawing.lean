module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Caps

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.HorizontalPlacement

open ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}
variable (s : ActiveStrip) (d : ProgressiveGraph.Diagram S V W .point) (idle : FixedCap S)

theorem start_active (i : Fin W) :
    (drawing s d idle).start (Fin.castAdd idle.profile.size i) = d.start i :=
  congrArg LocatedWire.start (wire_data_active s d idle i)

theorem finish_active (i : Fin W) :
    (drawing s d idle).finish (Fin.castAdd idle.profile.size i) = d.finish i :=
  congrArg LocatedWire.finish (wire_data_active s d idle i)

theorem start_idle (j : Fin idle.profile.size) :
    (drawing s d idle).start (Fin.natAdd W j) = none :=
  congrArg LocatedWire.start (wire_data_idle s d idle j)

theorem finish_idle (j : Fin idle.profile.size) :
    (drawing s d idle).finish (Fin.natAdd W j) = none :=
  congrArg LocatedWire.finish (wire_data_idle s d idle j)

section CapRead

variable {a : FixedCap S}
variable {old : Fin W → Option (Fin V)}
variable {new : Fin (W + idle.profile.size) → Option (Fin V)}
variable (onActive : ∀ w, new (Fin.castAdd idle.profile.size w) = old w)
variable (onIdle : ∀ j, new (Fin.natAdd W j) = none)
variable (cap : Fin a.profile.size ≃ {w : Fin W // old w = none})

theorem contacts_label (h : ∀ i, d.label (cap i).val = a.profile.label i)
    (i : Fin (adjoin s a idle).profile.size) :
    (drawing s d idle).label ((contacts onActive onIdle cap i).val) = (adjoin s a idle).profile.label i := by
  obtain ⟨i, rfl⟩ := (slots s a idle).symm.surjective i
  cases i with
  | inl j =>
    change (placedWires s d idle _).label = _
    rw [contacts_active, wire_data_active, active_slot_label]
    exact h j
  | inr j =>
    change (placedWires s d idle _).label = _
    rw [contacts_idle, wire_data_idle, idle_slot_label]

theorem contacts_x (y : ℝ) (h : ∀ i, d.x (cap i).val y = a.profile.x i)
    (i : Fin (adjoin s a idle).profile.size) :
    (drawing s d idle).x ((contacts onActive onIdle cap i).val) y = (adjoin s a idle).profile.x i := by
  obtain ⟨i, rfl⟩ := (slots s a idle).symm.surjective i
  cases i with
  | inl j =>
    change (placedWires s d idle _).wire.x y = _
    rw [contacts_active, wire_x_active, active_slot_x, h]
  | inr j =>
    change (placedWires s d idle _).wire.x y = _
    rw [contacts_idle, wire_x_idle, idle_slot_x]

end CapRead

variable {a b : FixedCap S} (p : FixedDrawing S a.profile b.profile)

def placed : FixedDrawing S (adjoin s a idle).profile (adjoin s b idle).profile where
  vertices := p.vertices
  wires := p.wires + idle.profile.size
  drawing := drawing s p.drawing idle
  input := contacts (start_active s p.drawing idle) (start_idle s p.drawing idle) p.input
  output := contacts (finish_active s p.drawing idle) (finish_idle s p.drawing idle) p.output
  input_label := contacts_label s p.drawing idle _ _ p.input p.input_label
  output_label := contacts_label s p.drawing idle _ _ p.output p.output_label
  input_x := contacts_x s p.drawing idle _ _ p.input 0 p.input_x
  output_x := contacts_x s p.drawing idle _ _ p.output 1 p.output_x

end Silmaril.RuntimeWires.Proofs.HorizontalPlacement
