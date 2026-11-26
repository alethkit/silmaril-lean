module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry.Thms
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry

open Core.Module (ListHeap)
open Core.Module.Functions (Session)
open Core.Module.SeededCall (Namespace)
open Core.Closure.Executor (CodeTable)

theorem ordinary_scalar_trace {scope : Source.Scope} (table : CodeTable) (session : Session)
    (actions : List (ModuleEntry.Action scope)) :
    ∃ reached completion,
      runPrefix table (actions.length + 1) (.ready session (actions.map .scalar)) =
        ([], .finished reached completion) ∧ reached.heap = session.heap ∧ reached.lists = session.lists :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.ordinary_scalar_trace table session actions

theorem seeded_scalar_carriers {scope : Source.Scope} (space : Namespace) (context : Seeded.CallContext)
    (actions : List (ModuleEntry.Action scope)) (lists : ListHeap) :
    let outcome := Seeded.runInstructionsIn space context (actions.map .scalar) lists
    outcome.heap = context.heap ∧ outcome.lists = lists ∧ outcome.calls = [] ∧
      outcome.residual.builtins = space.builtins :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.seeded_scalar_carriers space context actions lists

theorem seededSuite_carriers {scope : Source.Scope} (context : Seeded.CallContext)
    (incoming : Seeded.Observation) (actions : List (ModuleEntry.Action scope)) :
    let reached := (seededSuite context incoming actions).reached
    reached.heap = incoming.heap ∧ reached.lists = incoming.lists ∧ reached.calls = incoming.calls ∧
      reached.residual.builtins = incoming.residual.builtins := by
  have ⟨heap, lists, calls, builtins⟩ := seeded_scalar_carriers incoming.residual
    { context with heap := incoming.heap } actions incoming.lists
  exact ⟨heap, lists, by simp [seededSuite, calls], builtins⟩

open Functions.ExceptionalTry (Plan runSuite)

theorem runSuite_append {state failure action : Type}
    (step : state → action → Except failure state) (initial : state) (earlier later : List action) :
    runSuite step initial (earlier ++ later) =
      let first := runSuite step initial earlier
      match first.completion with
      | .ok () => runSuite step first.reached later
      | .error _ => first :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.runSuite_append step initial earlier later

theorem ordinary_reached_carriers {scope : Source.Scope} (session : Session)
    (plan : Plan (ModuleEntry.Action scope)) :
    let outcome := Compile.ModuleEntry.Functions.Run.runExceptionalTry session plan
    outcome.reached.heap = session.heap ∧ outcome.reached.lists = session.lists :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.ordinary_reached_carriers session plan

theorem ordinary_settlement {scope : Source.Scope} (table : CodeTable) (session : Session)
    (plan : Plan (ModuleEntry.Action scope)) (rest : List (Instruction scope)) :
    advance table (.ready session (.exceptionalTry plan :: rest)) =
      let outcome := Compile.ModuleEntry.Functions.Run.runExceptionalTry session plan
      ([], match outcome.completion with
        | .ok () => .ready outcome.reached rest
        | .error error => .finished outcome.reached error) := rfl

theorem seeded_reached_builtins {scope : Source.Scope} (space : Namespace) (plan : Plan (ModuleEntry.Action scope)) :
    (Seeded.runExceptionalTry space plan).reached.builtins = space.builtins :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.seeded_reached_builtins space plan

theorem seeded_settlement {scope : Source.Scope} (space : Namespace) (context : Seeded.CallContext)
    (plan : Plan (ModuleEntry.Action scope)) (rest : List (Instruction scope)) (lists : ListHeap) :
    Seeded.runInstructionsIn space context (.exceptionalTry plan :: rest) lists =
      let outcome := Seeded.runExceptionalTry space plan
      match outcome.completion with
      | .ok () => Seeded.runInstructionsIn outcome.reached context rest lists
      | .error error => ⟨outcome.reached, .error error, [], context.heap, lists⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.seeded_settlement space context plan rest lists

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry
