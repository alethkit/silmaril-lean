module

public import Silmaril.Semantics.RuntimeWires.SerialTrace.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.SerialTrace.Assembly

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.LayerSweep.Schedule

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W .point}
variable {s : d.LayerSweep} (p : s.Schedule)

/-- Every original wire has a distinct source name in the serial trace. -/
theorem origin_injective : Function.Injective p.origin :=
  Proofs.SerialTrace.origin_injective p

/-- Move the geometric source box to its scheduled row without changing
its output port number. Boundary port names are preserved. -/
theorem rename_origin (w : Fin W) : p.renameOrigin (s.origin w) = some (p.origin w) :=
  Proofs.SerialTrace.rename_origin p w

/-- Decoding any per-layer serialization reconstructs the original
labeled incidence in execution order, preserving port and cap order. -/
theorem trace_sheet : (s.serialSheet p).traceWires = p.expectedTrace :=
  Proofs.SerialTrace.trace_sheet p

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.LayerSweep.Schedule
