module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs

public section

namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ListConstruction

open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions
open Compile.ModuleEntry.Functions.Run
open Compile.ModuleEntry.Functions.Run.Seeded
open Core.Module (ListHeap ListObject)
open Core.Module.SeededCall (Namespace)

theorem constructList_ok_iff (space : Namespace) (heap : ListHeap) (argument : ListConstructorArgument)
    (object : ListObject) (updated : ListHeap) :
    constructList space heap argument = (.ok object, updated) ↔
      space.lookupGlobal "list" = some (.builtin .list) ∧
        let (contents, reached) := prepareListArgument heap argument
        reached.allocate contents = (object, updated) := by
  cases found : space.lookupGlobal "list" with
  | none => simp [constructList, found]
  | some callee =>
    cases callee with
    | builtin descriptor =>
      cases descriptor <;> simp [constructList, found]
      cases (prepareListArgument heap argument).2.allocate (prepareListArgument heap argument).1
      simp
    | _ => simp [constructList, found]

theorem run_assertListConstruction {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (lists : ListHeap) (test : ListConstructionTest scope) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.assertListConstruction test :: rest) lists =
      let outcome := evaluateListConstruction space lists test
      match outcome.checked with
      | .error error => ⟨space, .error (.ofCall error), [outcome.receipt], context.heap, outcome.lists⟩
      | .ok () =>
        let tail := runInstructionsIn space context rest outcome.lists
        { tail with calls := outcome.receipt :: tail.calls } := by
  simp only [runInstructionsIn, effectWithLists, ListConstructionOutcome.effect]
  cases (evaluateListConstruction space lists test).checked with
  | error _ => rfl
  | ok returned => cases returned; rfl

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ListConstruction
