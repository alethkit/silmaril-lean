module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
public import Silmaril.Languages.Python.Core.Module.SeededCall.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Silmaril.Languages.Python.Core.Module.SeededCall (Failure Namespace Value)
open Silmaril.Languages.Python.Core.Closure (Heap)
open Silmaril.Languages.Python.Core.Closure.Executor (CodeTable)
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run (Argument Instruction)
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

theorem observeArguments_iff {space : Namespace} {arguments : List Argument}
    {values : Except Failure (List Value)} {calls : List CallEvent} :
    observeArguments space arguments = (values, calls) ↔ EvaluatesArguments space arguments values calls := by
  constructor
  · induction arguments generalizing values calls with
    | nil =>
      intro observed
      cases observed
      exact .nil
    | cons argument rest ih =>
      intro observed
      cases first : observeArgument space argument with
      | mk result firstCalls =>
        cases result with
        | error error =>
          rw [observeArguments, first] at observed
          cases observed
          exact .stop first
        | ok value =>
          cases tail : observeArguments space rest with
          | mk tailValues tailCalls =>
            rw [observeArguments, first, tail] at observed
            cases observed
            exact .next first (ih tail)
  · intro evaluated
    induction evaluated with
    | nil => rfl
    | stop failed => simp [observeArguments, failed]
    | next first _ ih => simp [observeArguments, first, ih]

theorem preserves_storage {scope : Languages.Python.Source.Scope} (space : Namespace)
    (instructions : List (Instruction scope)) (table : CodeTable) (heap : Heap) :
    (runInstructions space instructions table heap).residual.builtins = space.builtins ∧
      (runInstructions space instructions table heap).heap = heap := by
  induction instructions generalizing space with
  | nil => exact ⟨rfl, rfl⟩
  | cons instruction rest ih =>
    cases selected : (effect space instruction table).binding with
    | error error => simp [runInstructions, selected]
    | ok binding =>
      cases binding with
      | none => simpa [runInstructions, selected] using ih space
      | some assignment =>
        obtain ⟨name, value⟩ := assignment
        simpa [runInstructions, selected, Namespace.bind_preserves_builtins] using
          ih (space.bindGlobal name value)

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
