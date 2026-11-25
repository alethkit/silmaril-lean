module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

public section

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Core.Module.SeededCall (Failure Namespace Value)

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
    observeNestedCall space destination name arguments = ⟨.error error, calls⟩ :=
  by simp [observeNestedCall, found, observeArguments_iff.mpr failed]

theorem run_preserves_builtins {source : Source.Module} (space : Namespace) (compiled : Compiled source) :
    (run space compiled).residual.builtins = space.builtins :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.preserves_builtins space compiled.instructions

theorem failing_instruction {scope : Source.Scope} {space : Namespace} {instruction : Instruction scope}
    {rest : List (Instruction scope)} {error : Failure}
    (failed : (effect space instruction).binding = .error error) :
    runInstructions space (instruction :: rest) = ⟨space, .error error, (effect space instruction).calls⟩ :=
  by simp [runInstructions, failed]

theorem assertNot_operand_failure {scope : Source.Scope} {space : Namespace}
    {operand : ModuleEntry.Operand scope} {error : Failure}
    (failed : evaluateScalar space false operand = .error error) :
    effect space (.assertNot operand) = ⟨.error error, []⟩ :=
  by simp [effect, assertOperand, failed, Except.bind, Except.map]

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
