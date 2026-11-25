module

public import Silmaril.Semantics.RuntimeWires.ProgressiveTrace.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveTrace.Sheet

public section

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
