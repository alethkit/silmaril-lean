module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
public import Silmaril.Languages.Python.Core.Module.SeededCall.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Silmaril.Languages.Python.Core.Module.SeededCall (Namespace)
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run (Instruction)
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

theorem preserves_builtins {scope : Languages.Python.Source.Scope} (space : Namespace)
    (instructions : List (Instruction scope)) :
    (runInstructions space instructions).residual.builtins = space.builtins := by
  induction instructions generalizing space with
  | nil => rfl
  | cons instruction rest ih =>
    cases selected : (effect space instruction).binding with
    | error error => simp [runInstructions, selected]
    | ok binding =>
      cases binding with
      | none => simpa [runInstructions, selected] using ih space
      | some assignment =>
        obtain ⟨name, value⟩ := assignment
        simpa [runInstructions, selected, Namespace.bind_preserves_builtins] using
          ih (space.bindGlobal name value)

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
