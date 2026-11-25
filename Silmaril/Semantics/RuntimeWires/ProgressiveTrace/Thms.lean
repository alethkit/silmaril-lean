module

public import Silmaril.Semantics.RuntimeWires.ProgressiveTrace.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveTrace.Sheet

public section

namespace Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

/-- On a list of distinct wire IDs, the decoder's port numbers coincide
with the positions of those IDs in the list. -/
theorem namePorts_map {I : Type*} [BEq I] [LawfulBEq I] (wires : List I) (nd : wires.Nodup)
    (label : I → O) (source : ℕ → WireOrigin) :
    namePorts source (wires.map label) = wires.map (fun w => (label w, source (wires.idxOf w))) :=
  Proofs.ProgressiveTrace.namePorts_map wires nd label source

/-- A local named-frontier invariant composes for the structural decoder. -/
theorem Sheet.traceWiresFrom_joinRows {n : ℕ} (word : Fin (n + 1) → List O)
    (row : ∀ i : Fin n, Row S (word i.castSucc) (word i.succ))
    (frontier : Fin (n + 1) → List (NamedWire O))
    (boxes : Fin n → List (BoxTrace S)) (offset : ℕ)
    (step : ∀ i, (row i).traceWires (offset + i.val) 0 (frontier i.castSucc) =
      ⟨frontier i.succ, boxes i⟩) :
    (ProgressiveGraph.Diagram.Sweep.joinRows word row).traceWiresFrom offset (frontier 0) =
      ⟨List.ofFn boxes, frontier (Fin.last n)⟩ :=
  Proofs.ProgressiveTrace.trace_joinRows word row frontier boxes offset step

end Silmaril.RuntimeWires.Sliced

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.Sweep

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W}
variable (s : d.Sweep)

/-- The source names distinguish all original geometric wires. -/
theorem origin_injective : Function.Injective s.origin :=
  Proofs.ProgressiveTrace.origin_injective s

/-- The named frontier is preserved exactly across each row, with the
original ordered inputs and outputs at that row's generator. -/
theorem trace_row (i : Fin V) :
    (s.row i).traceWires i.val 0 ((s.wires i.castSucc).map s.namedWire) =
      ⟨(s.wires i.succ).map s.namedWire, [s.expectedBox i]⟩ :=
  Proofs.ProgressiveTrace.row_trace s i

/-- Structural tracing of the bare composed sheet reconstructs the original
labeled wire incidence and port order, using the source-port renaming. -/
theorem trace_sheet : s.sheet.traceWires = s.expectedTrace :=
  Proofs.ProgressiveTrace.sheet_trace s

/-- A vertex-free sweep traces each ordered boundary input straight to its
corresponding output, with no generator events. -/
theorem trace_no_vertices {d : Diagram S 0 W} (s : d.Sweep) :
    s.sheet.traceWires = ⟨[], namePorts .boundary ((s.wires 0).map d.label)⟩ := by
  rfl

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.Sweep
