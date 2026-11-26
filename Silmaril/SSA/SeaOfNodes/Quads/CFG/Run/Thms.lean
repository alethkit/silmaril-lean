module

public import Silmaril.SSA.SeaOfNodes.Quads.CFG.Run.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.CFG.Run.Correctness

/-! # Checked-path adequacy and the terminator interface for target lowering -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.CFG

open Diamond (ValueSort Signature Model dataPorts)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {n : Nat}
variable {graph : Graph Op regs n} {source : Fin n}

/-- Taking an edge executes exactly the successor's ordered body on the
predecessor's final bank. -/
theorem Edge.take_eval (edge : Edge graph source) (path : Path graph source)
    (m : Model.{u, v, w} Op) (input : Bank m regs) :
    (edge.take path).eval m input = (graph.body edge.target).eval m (path.eval m input) :=
  Run.Proofs.take_eval edge path m input

/-- The path records the selected position even when two arms share a successor. -/
theorem Edge.take_occurrences (edge : Edge graph source) (path : Path graph source) :
    (edge.take path).occurrences = path.occurrences ++ [(edge.target.val, edge.slot)] :=
  Run.Proofs.take_occurrences edge path

/-- The total runner returns exactly the guard-selected path and the value read
by its final terminator. Every such checked return is the runner's outcome. -/
theorem Program.run_iff (program : Program graph out) (m : Model.{u, v, w} Op)
    (input : Bank m regs) (outcome : Outcome graph m out) :
    program.run m input = outcome ↔ program.Valid m input outcome :=
  Run.Proofs.run_iff program m input outcome

/-- The terminator reads the post-body version map to choose the same exact edge
or the same returned value as the source bank. -/
theorem Program.terminator_from_versions (program : Program graph out) (m : Model.{u, v, w} Op)
    (input : Bank m regs) (path : Path graph source) :
    ∃ values, path.values m input = some values ∧
      (readBank (dataPorts regs) (values.read (graph.versions source))).map
        ((program.terminator source).eval m) =
        some ((program.terminator source).eval m (path.eval m input)) :=
  Run.Proofs.terminator_from_versions program m input path

end Silmaril.SSA.SeaOfNodes.Quads.CFG
