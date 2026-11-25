module

public import Silmaril.Proofs.Semantics.RuntimeWires.SeamTrace.Move
public import Silmaril.Proofs.Semantics.RuntimeWires.SeamTrace.Support

public section

namespace Silmaril.RuntimeWires.Proofs.SeamTrace

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

private theorem wire_id (w : NamedWire O) : NamedWire.rename id w = w := by
  obtain ⟨label, origin⟩ := w
  cases origin <;> rfl

private theorem box_id (b : BoxOccurrence S) : BoxOccurrence.rename id b = b := by
  obtain ⟨site, ⟨e, i, o⟩⟩ := b
  simp only [BoxOccurrence.rename, BoxTrace.rename, id_eq]
  have identity : NamedWire.rename (O := O) id = id := funext wire_id
  simp [identity]

private theorem wire_comp (f g : BoxAddress → BoxAddress) (w : NamedWire O) :
    NamedWire.rename g (NamedWire.rename f w) = NamedWire.rename (g ∘ f) w := by
  obtain ⟨label, origin⟩ := w
  cases origin <;> rfl

private theorem box_comp (f g : BoxAddress → BoxAddress) (b : BoxOccurrence S) :
    BoxOccurrence.rename g (BoxOccurrence.rename f b) = BoxOccurrence.rename (g ∘ f) b := by
  obtain ⟨site, ⟨e, i, o⟩⟩ := b
  simp [BoxOccurrence.rename, BoxTrace.rename, List.map_map, Function.comp_def, wire_comp]

private theorem renamed_refl (t : SheetTrace S) : t.Renamed t id := by
  have boxes : BoxOccurrence.rename (S := S) id = id := funext box_id
  have wires : NamedWire.rename (O := O) id = id := funext wire_id
  constructor
  · rw [boxes, List.map_id]
  · rw [wires, List.map_id]

private theorem renamed_trans {s t u : SheetTrace S} {f g : BoxAddress → BoxAddress}
    (a : s.Renamed t f) (b : t.Renamed u g) : s.Renamed u (g ∘ f) := by
  have boxes : BoxOccurrence.rename (S := S) g ∘ BoxOccurrence.rename f =
      BoxOccurrence.rename (g ∘ f) := funext (box_comp f g)
  have wires : NamedWire.rename (O := O) g ∘ NamedWire.rename f =
      NamedWire.rename (g ∘ f) := funext (wire_comp f g)
  constructor
  · have h := (a.occurrences.map (BoxOccurrence.rename g)).trans b.occurrences
    simpa only [List.map_map, boxes] using h
  · have h := (congrArg (List.map (NamedWire.rename g)) a.outputs).trans b.outputs
    simpa only [List.map_map, wires] using h

theorem trace_seam {A B : List O} {p q : Sheet S A B} (same : Sheet.SeamEquivalent p q) :
    ∃ route, p.traceWires.Renamed q.traceWires route := by
  induction same with
  | rel _ _ move => exact trace_move_bare move
  | refl => exact ⟨id, renamed_refl _⟩
  | symm p q _ ih =>
    obtain ⟨f, trace⟩ := ih
    have bij := route_bijOn trace
    exact ⟨Function.invFunOn f p.traceWires.boxAddresses, inverse_trace p trace bij.injOn.leftInvOn_invFunOn⟩
  | trans _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨f, first⟩ := ih₁
    obtain ⟨g, second⟩ := ih₂
    exact ⟨g ∘ f, renamed_trans first second⟩

end Silmaril.RuntimeWires.Proofs.SeamTrace
