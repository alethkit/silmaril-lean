module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

public section

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Core.Module.SeededCall (Failure Namespace Value)
open Core.Module.Functions (TopFunction)
open Core.Closure (Heap)
open Core.Closure.Executor (CodeTable)

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
    (heap : Heap := .empty) :
    (run space compiled heap).residual.builtins = space.builtins :=
  (Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.preserves_storage
    space compiled.instructions compiled.table heap).1

theorem run_preserves_heap {source : Source.Module} (space : Namespace) (compiled : Compiled source)
    (heap : Heap) : (run space compiled heap).heap = heap :=
  (Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.preserves_storage
    space compiled.instructions compiled.table heap).2

theorem failing_instruction {scope : Source.Scope} {space : Namespace} {instruction : Instruction scope}
    {rest : List (Instruction scope)} {error : ModuleFailure}
    {table : CodeTable} {heap : Heap}
    (failed : (effect space instruction table).binding = .error error) :
    runInstructions space (instruction :: rest) table heap =
      ⟨space, .error error, (effect space instruction table).calls, heap⟩ :=
  by simp [runInstructions, failed]

theorem run_publication {scope : Source.Scope} {space : Namespace} {table : CodeTable} {heap : Heap}
    {name : String} {function : TopFunction} {rest : List (Instruction scope)}
    {definition : Core.Closure.Dispatch.Definition Core.Closure.Executor.Body function.ref.layout}
    (resolved : Core.Closure.Dispatch.resolve table function.ref = .ok definition) :
    runInstructions space (.publish name function :: rest) table heap =
      runInstructions (space.bindGlobal name (.function function.closure)) rest table heap :=
  by simp [runInstructions, effect, resolved, Except.map, Except.mapError]

theorem run_publication_fault {scope : Source.Scope} {space : Namespace} {table : CodeTable} {heap : Heap}
    {name : String} {function : TopFunction} {rest : List (Instruction scope)} {error : Core.Closure.Dispatch.Failure}
    (failed : Core.Closure.Dispatch.resolve table function.ref = .error error) :
    runInstructions space (.publish name function :: rest) table heap =
      ⟨space, .error (.publicationFault error), [], heap⟩ :=
  by simp [runInstructions, effect, failed, Except.map, Except.mapError]

theorem assertNot_operand_failure {scope : Source.Scope} {space : Namespace}
    {operand : ModuleEntry.Operand scope} {error : Failure}
    (failed : evaluateScalar space false operand = .error error) :
    effect space (.assertNot operand) = ⟨.error (.ofCall error), []⟩ :=
  by simp [effect, assertOperand, failed, Except.bind, Except.map, Except.mapError]

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
