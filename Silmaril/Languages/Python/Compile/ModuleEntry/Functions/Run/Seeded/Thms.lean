module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

public section

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Core.Module.SeededCall (Namespace)

theorem run_preserves_builtins {source : Source.Module} (space : Namespace) (compiled : Compiled source) :
    (run space compiled).residual.builtins = space.builtins :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.preserves_builtins space compiled.instructions

theorem failing_instruction {scope : Source.Scope} {space : Namespace} {instruction : Instruction scope}
    {rest : List (Instruction scope)} {error : Core.Module.SeededCall.Failure}
    (failed : (effect space instruction).binding = .error error) :
    runInstructions space (instruction :: rest) = ⟨space, .error error, (effect space instruction).call.toList⟩ :=
  by simp [runInstructions, failed]

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
