module

public import Silmaril.Languages.Starlark.Modules.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Init

public section

namespace Silmaril.Languages.Starlark.Modules

open Functions (Program)
open Lists (State)

/-- Exact agreement on command execution before publication or caller restoration. -/
theorem runs_iff_runCommands (program : Program) (host : Catalog) (commands : List Command)
    (state : State) (out : Result Unit) :
    Runs program host state commands out ↔ runCommands program host commands state = out :=
  ⟨Proofs.Languages.Starlark.Modules.eq_commands_of_run,
    fun h => h ▸ Proofs.Languages.Starlark.Modules.commands_run program host commands state⟩

/-- Exact adequacy of validation, initialization, imports and publication. -/
theorem initializes_iff_initialize (program : Program) (host : Catalog) (source : Source)
    (caller : State) (out : Result Published) :
    Initializes program host source caller out ↔ initializeModule program host source caller = out :=
  ⟨Proofs.Languages.Starlark.Modules.eq_initialize_of_initializes,
    fun h => h ▸ Proofs.Languages.Starlark.Modules.initializes_initialize program host source caller⟩

end Silmaril.Languages.Starlark.Modules
