module

public import Silmaril.Semantics.RuntimeWires.TiedHeightSweep.Thms
public import Silmaril.Semantics.RuntimeWires.SlicedTrace.Defs

@[expose] public section

/-!
# Structural trace of the tied-height geometric sheet

This recovers labeled wire incidence and ordered ports for the progressive
point-vertex fragment of Definition 3.2 (p. 9:6) in Mario Román and Paweł
Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5. The expected trace is specified using the source
diagram. The decoder being compared reads only the typed sheet.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.LayerSweep

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W .point}
variable (s : d.LayerSweep)

/-- The horizontal box ordinal at the vertex's event level. This counts
vertices with empty ports and skips passing strand cells. -/
noncomputable def boxOrdinal (v : Fin V) : ℕ :=
  (s.layer (d.levelIndex v)).vertices.idxOf v

/-- Rename an original wire ID by its source port in the geometric sheet. -/
noncomputable def origin (w : Fin W) : WireOrigin :=
  match d.start w with
  | none => .boundary ((s.wires 0).idxOf w)
  | some v => .box (d.levelIndex v).val (s.boxOrdinal v) ((d.outputs v).idxOf w)

noncomputable def namedWire (w : Fin W) : NamedWire O := (d.label w, s.origin w)

/-- The original labeled incidence at a vertex, in its given port order. -/
noncomputable def expectedBox (v : Fin V) : BoxTrace S :=
  ⟨d.generator v, (d.inputs v).map s.namedWire, (d.outputs v).map s.namedWire⟩

/-- The expected trace from the drawing, after source-port renaming. -/
noncomputable def expectedTrace : SheetTrace S :=
  ⟨List.ofFn (fun i => (s.layer i).vertices.map s.expectedBox),
    (s.wires (Fin.last d.levelCount)).map s.namedWire⟩

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.LayerSweep
