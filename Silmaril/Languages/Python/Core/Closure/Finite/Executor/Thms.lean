module

public import Silmaril.Languages.Python.Core.Closure.Finite.Executor.Defs
import Silmaril.Proofs.Languages.Python.Core.Closure.Finite.Executor.Correspondence

public section

namespace Silmaril.Languages.Python.Core.Closure.Finite.Executor

open Closure.Executor (Event)
open Semantics.Operational

/-- A finite step computes the exact Core label and full projected state,
including the residual heap, saved stack and current control. -/
theorem advance_project (rows : CodeRows) (source : State) :
    (advance rows source).map Transition.project = Closure.Executor.advance rows.project source.project :=
  Proofs.Languages.Python.Core.Closure.Finite.Executor.advance_project rows source

theorem advance_none_iff (rows : CodeRows) (source : State) :
    advance rows source = none ↔ Closure.Executor.advance rows.project source.project = none := by
  rw [← advance_project rows source]
  cases advance rows source <;> simp

theorem observes_iff (source : State) (result : Result) :
    Closure.Executor.observes source.project result ↔ source.completion? = some result := by
  cases source <;> simp [State.project, Closure.Executor.observes, State.completion?]

theorem projection (rows : CodeRows) : Projection (presented rows) (semantic rows.project) State.project id :=
  Proofs.Languages.Python.Core.Closure.Finite.Executor.projection rows

theorem step_iff {rows : CodeRows} {source : State} {label : Option Event}
    {target : Closure.Executor.State} :
    (semantic rows.project).Tr source.project label target ↔
      ∃ successor, advance rows source = some (label, successor) ∧ successor.project = target :=
  Proofs.Languages.Python.Core.Closure.Finite.Executor.step_iff

/-- Recover each intermediate finite witness and preserve the entire
label sequence, including silent steps. -/
theorem execution_readback {rows : CodeRows} {source : State} {labels : List (Option Event)}
    {target : Closure.Executor.State} {states : List Closure.Executor.State}
    (run : (semantic rows.project).Execution source.project labels target states) :
    ∃ final witnesses, (presented rows).Execution source labels final witnesses ∧
      witnesses.map State.project = states ∧ final.project = target :=
  Proofs.Languages.Python.Core.Closure.Finite.Executor.execution_readback run

theorem runPrefix_project (rows : CodeRows) (fuel : Nat) (source : State) :
    let next := runPrefix rows fuel source
    (next.1, next.2.project) = Closure.Executor.runPrefix rows.project fuel source.project :=
  Proofs.Languages.Python.Core.Closure.Finite.Executor.runPrefix_project rows fuel source

end Silmaril.Languages.Python.Core.Closure.Finite.Executor
