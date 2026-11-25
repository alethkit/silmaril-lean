module

public import Silmaril.Languages.Python.Core.Closure.Finite.Executor.Defs
import Silmaril.Proofs.Languages.Python.Core.Closure.Finite.Executor.Correspondence

public section

namespace Silmaril.Languages.Python.Core.Closure.Finite.Executor

open Closure.Executor (Event GlobalLookup)
open Semantics.Operational

/-- A finite step computes the exact Core label and full projected state,
including the residual heap, saved stack and current control. -/
theorem advanceIn_project (rows : CodeRows) (globals : GlobalLookup) (source : State) :
    (advanceIn rows globals source).map Transition.project =
      Closure.Executor.advanceIn rows.project globals source.project :=
  Proofs.Languages.Python.Core.Closure.Finite.Executor.advanceIn_project rows globals source

theorem advanceIn_none_iff (rows : CodeRows) (globals : GlobalLookup) (source : State) :
    advanceIn rows globals source = none ↔ Closure.Executor.advanceIn rows.project globals source.project = none := by
  rw [← advanceIn_project rows globals source]
  cases advanceIn rows globals source <;> simp

theorem observes_iff (source : State) (result : Result) :
    Closure.Executor.observes source.project result ↔ source.completion? = some result := by
  cases source <;> simp [State.project, Closure.Executor.observes, State.completion?]

theorem projectionIn (rows : CodeRows) (globals : GlobalLookup) :
    Projection (presentedIn rows globals) (semanticIn rows.project globals) State.project id :=
  Proofs.Languages.Python.Core.Closure.Finite.Executor.projectionIn rows globals

theorem stepIn_iff {rows : CodeRows} {globals : GlobalLookup} {source : State} {label : Option Event}
    {target : Closure.Executor.State} :
    (semanticIn rows.project globals).Tr source.project label target ↔
      ∃ successor, advanceIn rows globals source = some (label, successor) ∧ successor.project = target :=
  Proofs.Languages.Python.Core.Closure.Finite.Executor.stepIn_iff

/-- Recover each intermediate finite witness and preserve the entire
label sequence, including silent steps. -/
theorem executionIn_readback {rows : CodeRows} {globals : GlobalLookup} {source : State} {labels : List (Option Event)}
    {target : Closure.Executor.State} {states : List Closure.Executor.State}
    (run : (semanticIn rows.project globals).Execution source.project labels target states) :
    ∃ final witnesses, (presentedIn rows globals).Execution source labels final witnesses ∧
      witnesses.map State.project = states ∧ final.project = target :=
  Proofs.Languages.Python.Core.Closure.Finite.Executor.executionIn_readback run

theorem runPrefixIn_project (rows : CodeRows) (globals : GlobalLookup) (fuel : Nat) (source : State) :
    let next := runPrefixIn rows globals fuel source
    (next.1, next.2.project) = Closure.Executor.runPrefixIn rows.project globals fuel source.project :=
  Proofs.Languages.Python.Core.Closure.Finite.Executor.runPrefixIn_project rows globals fuel source

theorem advance_project (rows : CodeRows) (source : State) :
    (advance rows source).map Transition.project = Closure.Executor.advance rows.project source.project :=
  advanceIn_project rows Closure.Executor.emptyGlobals source

theorem advance_none_iff (rows : CodeRows) (source : State) :
    advance rows source = none ↔ Closure.Executor.advance rows.project source.project = none :=
  advanceIn_none_iff rows Closure.Executor.emptyGlobals source

theorem projection (rows : CodeRows) : Projection (presented rows) (semantic rows.project) State.project id :=
  projectionIn rows Closure.Executor.emptyGlobals

theorem step_iff {rows : CodeRows} {source : State} {label : Option Event}
    {target : Closure.Executor.State} :
    (semantic rows.project).Tr source.project label target ↔
      ∃ successor, advance rows source = some (label, successor) ∧ successor.project = target :=
  stepIn_iff

theorem execution_readback {rows : CodeRows} {source : State} {labels : List (Option Event)}
    {target : Closure.Executor.State} {states : List Closure.Executor.State}
    (run : (semantic rows.project).Execution source.project labels target states) :
    ∃ final witnesses, (presented rows).Execution source labels final witnesses ∧
      witnesses.map State.project = states ∧ final.project = target :=
  executionIn_readback run

theorem runPrefix_project (rows : CodeRows) (fuel : Nat) (source : State) :
    let next := runPrefix rows fuel source
    (next.1, next.2.project) = Closure.Executor.runPrefix rows.project fuel source.project :=
  runPrefixIn_project rows Closure.Executor.emptyGlobals fuel source

end Silmaril.Languages.Python.Core.Closure.Finite.Executor
