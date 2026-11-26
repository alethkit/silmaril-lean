module

public import Silmaril.SSA.SeaOfNodes.Quads.CFG.Run.Defs
import Silmaril.SSA.SeaOfNodes.Quads.CFG.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.CFG.Run.Proofs

open Diamond (ValueSort Signature Model dataPorts)
open Join (Block)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {n : Nat}
variable {graph : Graph Op regs n} {source : Fin n}

private theorem eval_beforeLatest {prior : Graph Op regs n} {preds : Predecessors n}
    {body : Block Op regs} {j : Fin (n + 1)} (path : Path (.snoc prior preds body) j)
    (bound : j.val < n) (m : Model.{u, v, w} Op) (input : Bank m regs) :
    (path.beforeLatest bound).eval m input = path.eval m input := by
  cases path with
  | earlier _ => rfl
  | edge _ _ => exact (Nat.lt_irrefl _ bound).elim

private theorem start_eval (graph : Graph Op regs n) (m : Model.{u, v, w} Op)
    (input : Bank m regs) :
    graph.start.2.eval m input = (graph.body graph.start.1).eval m input := by
  induction graph with
  | entry _ => rfl
  | snoc prior preds body ih =>
    simpa [Graph.start, Graph.body, Path.eval] using ih

theorem take_eval (edge : Edge graph source) (path : Path graph source)
    (m : Model.{u, v, w} Op) (input : Bank m regs) :
    (edge.take path).eval m input = (graph.body edge.target).eval m (path.eval m input) := by
  induction edge with
  | @latest _ _ _ body occurrence =>
    simpa [Edge.take, Edge.target, Graph.body, Path.eval, Path.unlift] using
      congrArg (Block.eval body m) (eval_beforeLatest path (Predecessors.get _ occurrence).isLt m input)
  | earlier edge ih =>
    simpa [Edge.take, Edge.target, Graph.body, Path.eval, Path.unlift, eval_beforeLatest] using
      ih path.unlift

private theorem occurrences_beforeLatest {prior : Graph Op regs n} {preds : Predecessors n}
    {body : Block Op regs} {j : Fin (n + 1)} (path : Path (.snoc prior preds body) j)
    (bound : j.val < n) :
    (path.beforeLatest bound).occurrences = path.occurrences := by
  cases path with
  | earlier _ => rfl
  | edge _ _ => exact (Nat.lt_irrefl _ bound).elim

theorem take_occurrences (edge : Edge graph source) (path : Path graph source) :
    (edge.take path).occurrences = path.occurrences ++ [(edge.target.val, edge.slot)] := by
  induction edge with
  | latest occurrence =>
    simp [Edge.take, Edge.target, Edge.slot, Path.occurrences, Path.unlift, occurrences_beforeLatest]
  | earlier edge ih =>
    simpa [Edge.take, Edge.target, Edge.slot, Path.occurrences, Path.unlift, occurrences_beforeLatest]
      using ih path.unlift

variable (program : Program graph out) (m : Model.{u, v, w} Op) (input : Bank m regs)

private theorem soundFrom (i : Fin n) (path : Path graph i) (follows : program.Follows m input path) :
    program.Valid m input (program.runFrom m i path (path.eval m input)) := by
  rw [Program.runFrom]
  split
  · rename_i result returned
    exact ⟨follows, returned⟩
  · rename_i edge taken
    rw [← take_eval edge path m input]
    exact soundFrom edge.target (edge.take path) (.edge follows edge taken)
termination_by n - i.val
decreasing_by
  have forward := (‹Edge graph i›).forward
  omega

private theorem follows_runFrom {i : Fin n} {path : Path graph i}
    (follows : program.Follows m input path) :
    program.runFrom m i path (path.eval m input) = program.run m input := by
  induction follows with
  | entry => simp only [Program.run, start_eval]
  | @edge i path prior edge taken ih =>
    calc
      _ = program.runFrom m i path (path.eval m input) := by
        symm
        rw [Program.runFrom, taken, take_eval edge path m input]
      _ = _ := ih

theorem run_iff (outcome : Outcome graph m out) :
    program.run m input = outcome ↔ program.Valid m input outcome := by
  constructor
  · intro same
    subst outcome
    simpa only [Program.run, start_eval] using soundFrom program m input _ graph.start.2 .entry
  · rcases outcome with ⟨block, path, result⟩
    rintro ⟨follows, returned⟩
    rw [← follows_runFrom program m input follows, Program.runFrom]
    simp [returned]

theorem terminator_from_versions {i : Fin n} (path : Path graph i) :
    ∃ values, path.values m input = some values ∧
      (readBank (dataPorts regs) (values.read (graph.versions i))).map ((program.terminator i).eval m) =
        some ((program.terminator i).eval m (path.eval m input)) := by
  obtain ⟨values, defined, bank⟩ := path.versions_agree m input
  exact ⟨values, defined, congrArg (fun b => b.map ((program.terminator i).eval m)) bank⟩

end Silmaril.SSA.SeaOfNodes.Quads.CFG.Run.Proofs
