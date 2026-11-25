module

public import Silmaril.Semantics.RuntimeWires.ProgressiveSweep.Thms
public import Silmaril.Semantics.RuntimeWires.SlicedTrace.Defs

@[expose] public section

/-!
# Wire incidence from the traced sheet

This is a comparison with the labeled progressive plane graphs of
Definition 3.2 in Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5 (p. 9:6).
The trace uses the syntax of the composed sheet and records its
ordered, labeled incidence.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.Sweep

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W}
variable (s : d.Sweep)

/-- Name an original geometric wire by the cap or generator port where it starts. -/
noncomputable def origin (w : Fin W) : WireOrigin :=
  match d.start w with
  | none => .boundary ((s.wires 0).idxOf w)
  | some v => .box (d.vertexOrder.symm v).val 0 ((d.outputs v).idxOf w)

noncomputable def namedWire (w : Fin W) : NamedWire O := (d.label w, s.origin w)

/-- The original ordered ports and generator label at the event of a row. -/
noncomputable def expectedBox (i : Fin V) : BoxTrace S :=
  let v := d.vertexOrder i
  ⟨d.generator v, (d.inputs v).map s.namedWire, (d.outputs v).map s.namedWire⟩

/-- The labeled incidence read directly from the original graph in sweep order. -/
noncomputable def expectedTrace : SheetTrace S :=
  ⟨List.ofFn (fun i => [s.expectedBox i]), (s.wires (Fin.last V)).map s.namedWire⟩

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.Sweep
