module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
public import Silmaril.Languages.Python.Core.Module.Functions.Thms
public import Silmaril.Languages.Python.Core.Module.SeededCall.Thms
public import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Thms
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

public section

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Core.Module.SeededCall (CallObservation Delivers Expectation Failure Namespace Raised Value)
open Core.Module.Functions (TopFunction)
open Core.Closure (Function Heap)
open Core.Closure.Executor (Fault labelledIn)

theorem observeArguments_iff {space : Namespace} {arguments : List Argument}
    {values : Except Failure (List Value)} {calls : List CallEvent} :
    observeArguments space arguments = (values, calls) ↔ EvaluatesArguments space arguments values calls :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.observeArguments_iff

theorem observeNestedCall_missing {space : Namespace} {destination : Core.Module.Functions.Destination}
    {name : String} {arguments : List Argument} (missing : space.lookupGlobal name = none) :
    observeNestedCall space destination name arguments = ⟨.error (.raised (.runtime (.nameError name))), []⟩ :=
  by simp [observeNestedCall, missing]

theorem observeNestedCall_failedArguments {space : Namespace} {destination : Core.Module.Functions.Destination}
    {name : String} {callee : Value} {arguments : List Argument} {error : Failure} {calls : List CallEvent}
    (found : space.lookupGlobal name = some callee)
    (failed : EvaluatesArguments space arguments (.error error) calls) :
    observeNestedCall space destination name arguments = ⟨.error (.ofCall error), calls⟩ :=
  by simp [observeNestedCall, found, observeArguments_iff.mpr failed]

theorem run_preserves_builtins {source : Source.Module} (space : Namespace) (compiled : Compiled source)
    (heap : Heap := .empty) (fuel : Nat := 1000) :
    (run space compiled heap fuel).residual.builtins = space.builtins :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.preserves_builtins
    space compiled.instructions ⟨compiled.table, heap, fuel, []⟩

theorem callback_path (space : Namespace) (context : CallContext) (closure : Function) :
    let invocation := callbackInvocation space context.heap closure
    let (events, residual) := invocation.runPrefix context.table context.fuel
    (labelledIn context.table (callbackSession space context.heap).globals).Path
      invocation.state events residual.state :=
  (callbackInvocation space context.heap closure).run_path context.table context.fuel

theorem callback_delivers {space : Namespace} {expectation : Expectation}
    {heap residual : Heap} {result : Core.Closure.Result} {observation : CallObservation} :
    observeCallback space expectation (.finished heap result) = (.ok observation, residual) ↔
      let inner := (result.map seededValue).mapError (callbackError space)
      Delivers expectation inner observation.result ∧
        observation.caught = expectation.caught? inner ∧ residual = heap := by
  cases observation
  simp [observeCallback, Expectation.delivers_iff.symm, eq_comm, and_assoc]

theorem invokeCall_published {space : Namespace} {context : CallContext} {closure : Function}
    (expectation : Expectation)
    {definition : Core.Closure.Dispatch.Definition Core.Closure.Executor.Body closure.code.layout}
    (published : closure ∈ context.published)
    (resolved : Core.Closure.Dispatch.resolve context.table closure.code = .ok definition)
    (noParameters : definition.parameters.slots = []) :
    invokeCall space context (.helper (.assertRaises expectation.onReturn))
        [.exceptionClass expectation.expected, .function closure] =
      invokeCallback space context expectation closure := by
  cases expectation
  simp [invokeCall, CallContext.acceptsPublishedCall, Core.Module.SeededCall.Request.decode, published, resolved,
    noParameters]

theorem callback_fault (space : Namespace) (expectation : Expectation) (heap : Heap)
    (stack : Core.Closure.Executor.Stack) (fault : Fault) :
    observeCallback space expectation (.faulted heap stack fault) = (.error (.callbackFault fault), heap) := rfl

theorem callback_seedOnlyGlobal {space : Namespace} {heap : Heap} {name : String} {value : Value}
    (found : space.lookupGlobal name = some value) (unsupported : ordinaryValue? value = none) :
    (callbackSession space heap).globals name = none ∧
      callbackError space (.nameError name) = .unsupported := by
  simp [callbackSession, callbackError, found, unsupported]

theorem failing_instruction {scope : Source.Scope} {space : Namespace} {instruction : Instruction scope}
    {rest : List (Instruction scope)} {error : ModuleFailure}
    {context : CallContext} (failed : (effect space context instruction).1.binding = .error error) :
    runInstructionsIn space context (instruction :: rest) =
      ⟨space, .error error, (effect space context instruction).1.calls, (effect space context instruction).2⟩ :=
  by simp [runInstructionsIn, failed]

/-- Settle one direct discard call from the actual executor state. A
finished call emits one receipt before its tail, and a failed call skips the tail. -/
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
        ⟨space, .error .directCallFuelExhausted, [], heap⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.run_directDiscard found admitted

theorem run_directDiscard_unsupported {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {closure : Function} {rest : List (Instruction scope)}
    (found : space.lookupGlobal name = some (.function closure))
    (rejected : context.acceptsPublishedCall closure = false) :
    runInstructionsIn space context (.call .discard name [] :: rest) =
      ⟨space, .error .unsupported, [⟨name, ⟨.error .unsupported, none⟩⟩], context.heap⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.run_directDiscard_unsupported found rejected

theorem run_publication {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {function : TopFunction} {rest : List (Instruction scope)}
    {definition : Core.Closure.Dispatch.Definition Core.Closure.Executor.Body function.ref.layout}
    (resolved : Core.Closure.Dispatch.resolve context.table function.ref = .ok definition) :
    runInstructionsIn space context (.publish name function :: rest) =
      runInstructionsIn (space.bindGlobal name (.function function.closure))
        { context with published := function.closure :: context.published } rest :=
  by simp [runInstructionsIn, effect, resolved, Except.map, Except.mapError]

theorem run_publication_fault {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {name : String} {function : TopFunction} {rest : List (Instruction scope)} {error : Core.Closure.Dispatch.Failure}
    (failed : Core.Closure.Dispatch.resolve context.table function.ref = .error error) :
    runInstructionsIn space context (.publish name function :: rest) =
      ⟨space, .error (.publicationFault error), [], context.heap⟩ :=
  by simp [runInstructionsIn, effect, failed, Except.map, Except.mapError]

theorem assertNot_operand_failure {scope : Source.Scope} {space : Namespace} {context : CallContext}
    {operand : ModuleEntry.Operand scope} {error : Failure}
    (failed : evaluateScalar space false operand = .error error) :
    effect space context (.assertNot operand) = (⟨.error (.ofCall error), []⟩, context.heap) :=
  by simp [effect, assertOperand, failed, Except.bind, Except.map, Except.mapError]

theorem effect_assertVarNames {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (receiver : String) (needle : List UInt32) :
    effect space context (.assertVarNames receiver needle : Instruction scope) =
      (⟨(checkVarNames space context.table receiver needle).map fun _ => none, []⟩, context.heap) := rfl

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
