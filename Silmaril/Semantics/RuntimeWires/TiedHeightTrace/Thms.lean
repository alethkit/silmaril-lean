module

public import Silmaril.Semantics.RuntimeWires.TiedHeightTrace.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.TiedHeightTrace.Sheet

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.LayerSweep

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W .point}
variable (s : d.LayerSweep)

/-- Source ports distinguish all original wires. -/
theorem origin_injective : Function.Injective s.origin :=
  Proofs.TiedHeightTrace.origin_injective s

/-- A layer's structural trace preserves the named frontier and records
every generator's ordered ports, including generators with empty ports. -/
theorem trace_row (i : Fin d.levelCount) :
    (s.row i).traceWires i.val 0 ((s.wires i.castSucc).map s.namedWire) =
      ⟨(s.wires i.succ).map s.namedWire, (s.layer i).vertices.map s.expectedBox⟩ :=
  Proofs.TiedHeightTrace.row_trace s i

/-- The structural decoder of the bare geometric sheet reads the original
labeled incidence and ordered ports after injective source-port renaming. -/
theorem trace_sheet : s.sheet.traceWires = s.expectedTrace :=
  Proofs.TiedHeightTrace.sheet_trace s

/-- A cap-to-cap wire keeps the name of its input port in the final frontier. -/
theorem trace_cap_to_cap (w : Fin W) (starts : d.start w = none) (ends : d.finish w = none) :
    (d.label w, .boundary ((s.wires 0).idxOf w)) ∈ s.sheet.traceWires.outputs := by
  rw [s.trace_sheet]
  exact List.mem_map.mpr ⟨w, (s.output_mem w).mpr ends, by simp [namedWire, origin, starts]⟩

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.LayerSweep
