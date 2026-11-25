module

public import Silmaril.Languages.Starlark.Modules.Loader.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Loader.Eval

public section

namespace Silmaril.Languages.Starlark.Modules.Loader

open Functions (Program)

/-- The loader rules give the exact result, publication cache and final state. -/
theorem runs_iff_denote (program : Program) (manifest : Manifest) (active : List ModuleId)
    {α : Type} (job : Job α) (s : Session) (out : Result α) :
    Runs program manifest active job s out ↔ denote program manifest active job s = out :=
  ⟨Proofs.Languages.Starlark.Modules.Loader.denote_eq_of_runs,
    fun h => h ▸ Proofs.Languages.Starlark.Modules.Loader.runs_denote program manifest active job s⟩

end Silmaril.Languages.Starlark.Modules.Loader
