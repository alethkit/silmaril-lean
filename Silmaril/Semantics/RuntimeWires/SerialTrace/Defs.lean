module

public import Silmaril.Semantics.RuntimeWires.TiedHeightTrace.Thms

@[expose] public section

/-!
# Structural trace of serial layer schedules

This recovers labeled incidence and ordered ports for serializations of the
progressive point-vertex fragment of Definition 3.2 (p. 9:6) in Mario Román
and Paweł Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5. The underlying decoder traverses only the typed sheet.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {kind : VertexSeparation}

/-- The wire IDs of one vertex block before or after it executes. -/
def vertexWires (d : Diagram S V W kind) (j : Fin V) : Bool → List (Fin W)
  | false => d.inputs j
  | true => d.outputs j

/-- Wire IDs at the completed-slot frontier in its original horizontal order. -/
def frontierWires (d : Diagram S V W kind) (done : Finset (Fin V)) :
    List (LayerSlot V W) → List (Fin W)
  | [] => []
  | .inl w :: tail => w :: d.frontierWires done tail
  | .inr j :: tail => d.vertexWires j (decide (j ∈ done)) ++ d.frontierWires done tail

namespace LayerSweep.Schedule

variable {d : Diagram S V W .point} {s : d.LayerSweep} (p : s.Schedule)

/-- The global execution order, obtained by concatenating the layer schedules. -/
noncomputable def vertices : List (Fin V) :=
  (List.ofFn p.order).flatten

/-- The actual row of a vertex in the composed serial sheet. -/
noncomputable def serialRow (v : Fin V) : ℕ := p.vertices.idxOf v

/-- A serial source port keeps its port index and uses its scheduled row.
Every executed box has ordinal zero in its own row. -/
noncomputable def origin (w : Fin W) : WireOrigin :=
  match d.start w with
  | none => .boundary ((s.wires 0).idxOf w)
  | some v => .box (p.serialRow v) 0 ((d.outputs v).idxOf w)

/-- Translate a geometric source name into its serial row and box ordinal.
An invalid geometric row or box index has no translation. -/
noncomputable def renameOrigin : WireOrigin → Option WireOrigin
  | .boundary port => some (.boundary port)
  | .box row box port =>
    if h : row < d.levelCount then
      ((s.layer ⟨row, h⟩).vertices[box]?).map (fun v => .box (p.serialRow v) 0 port)
    else none

noncomputable def namedWire (w : Fin W) : NamedWire O := (d.label w, p.origin w)

noncomputable def expectedBox (v : Fin V) : BoxTrace S :=
  ⟨d.generator v, (d.inputs v).map p.namedWire, (d.outputs v).map p.namedWire⟩

/-- Original incidence in execution order, with port order preserved. -/
noncomputable def expectedTrace : SheetTrace S :=
  ⟨p.vertices.map (fun v => [p.expectedBox v]),
    (s.wires (Fin.last d.levelCount)).map p.namedWire⟩

end LayerSweep.Schedule
end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
