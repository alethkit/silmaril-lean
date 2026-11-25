module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
public import Silmaril.Languages.Python.Core.Module.SeededCall.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Silmaril.Languages.Python.Core.Module.SeededCall (Failure Namespace Value)
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

theorem preserves_builtins {scope : Languages.Python.Source.Scope} (space : Namespace)
    (instructions : List (Instruction scope)) (context : CallContext) :
    (runInstructionsIn space context instructions).residual.builtins = space.builtins := by
  induction instructions generalizing space context with
  | nil => rfl
  | cons instruction rest ih =>
    cases selected : (effect space context instruction).1.binding with
    | error error => simp [runInstructionsIn, selected]
    | ok binding =>
      cases binding with
      | none => simp [runInstructionsIn, selected, ih]
      | some assignment =>
        obtain ⟨name, value⟩ := assignment
        simp [runInstructionsIn, selected, ih, Namespace.bind_preserves_builtins]

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
