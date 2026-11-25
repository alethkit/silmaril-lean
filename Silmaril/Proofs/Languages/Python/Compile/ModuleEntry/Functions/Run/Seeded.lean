module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
public import Silmaril.Languages.Python.Core.Module.SeededCall.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Silmaril.Languages.Python.Core.Module.SeededCall (Failure Namespace Value)
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run (Argument Instruction)
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Core.Closure (Function)

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


theorem run_directDiscard {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {closure : Function} {rest : List (Instruction scope)}
    (found : space.lookupGlobal name = some (.function closure))
    (admitted : context.acceptsPublishedCall closure = true) :
    runInstructionsIn space context (.call .discard name [] :: rest) =
      let invocation := callbackInvocation space context.heap closure
      match (invocation.runPrefix context.table context.fuel).2.state with
      | .finished heap (.ok value) =>
        let tail := runInstructionsIn space { context with heap } rest
        { tail with calls := ⟨name, ⟨.ok (seededValue value), none⟩⟩ :: tail.calls }
      | .finished heap (.error error) =>
        let failure := callbackError space error
        ⟨space, .error (.ofCall failure), [⟨name, ⟨.error failure, none⟩⟩], heap⟩
      | .faulted heap _ fault => ⟨space, .error (.directCallFault fault), [], heap⟩
      | .running heap .. | .delivering heap .. | .receiving heap .. =>
        ⟨space, .error .directCallFuelExhausted, [], heap⟩ := by
  simp [runInstructionsIn, effect, Core.Module.SeededCall.resolveCall,
    Core.Module.SeededCall.Operand.eval, found, Core.Module.SeededCall.Operand.evalList,
    Except.bind, Except.map, invokeFlatCall, admitted]
  generalize (callbackInvocation space context.heap closure |>.runPrefix context.table context.fuel).2.state =
    state
  cases state with
  | finished heap result => cases result <;> rfl
  | _ => rfl

theorem run_directDiscard_unsupported {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {closure : Function} {rest : List (Instruction scope)}
    (found : space.lookupGlobal name = some (.function closure))
    (rejected : context.acceptsPublishedCall closure = false) :
    runInstructionsIn space context (.call .discard name [] :: rest) =
      ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], context.heap⟩ := by
  simp [runInstructionsIn, effect, Core.Module.SeededCall.resolveCall,
    Core.Module.SeededCall.Operand.eval, found, Core.Module.SeededCall.Operand.evalList,
    Except.bind, Except.map, Except.mapError, invokeFlatCall, rejected, acceptObservation, ModuleFailure.ofCall]

theorem run_adjacentKeywordDiscard {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {closure : Function} {value : Int} {rest : List (Instruction scope)}
    (found : space.lookupGlobal name = some (.function closure))
    (admitted : context.acceptsPublishedCall closure 1 = true) :
    runInstructionsIn space context (.adjacentKeywordDiscard name value :: rest) =
      let invocation := (callbackSession space context.heap).prepareCall .discard
        (.literal (.function closure)) [.literal (.int value)]
      match (invocation.runPrefix context.table context.fuel).2.state with
      | .finished heap (.ok result) =>
        let tail := runInstructionsIn space { context with heap } rest
        { tail with calls := ⟨name, ⟨.ok (seededValue result), none⟩⟩ :: tail.calls }
      | .finished heap (.error error) =>
        let failure := callbackError space error
        ⟨space, .error (.ofCall failure), [⟨name, ⟨.error failure, none⟩⟩], heap⟩
      | .faulted heap _ fault => ⟨space, .error (.directCallFault fault), [], heap⟩
      | .running heap .. | .delivering heap .. | .receiving heap .. =>
        ⟨space, .error .directCallFuelExhausted, [], heap⟩ :=
  by
    simp [runInstructionsIn, effect, invokeAdjacentKeywordDiscard, found, admitted]
    generalize (((callbackSession space context.heap).prepareCall .discard
      (.literal (.function closure)) [.literal (.int value)]).runPrefix context.table context.fuel).2.state =
      state
    cases state with
    | finished heap result => cases result <;> rfl
    | _ => rfl

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
