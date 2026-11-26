module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Module

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings

open Block (ModuleBinders)

/-- Starting from actual module entry, derive all reached source steps
from the static schedule and checked compilation. -/
theorem checked_trace {commands : List Command} (profile : Profile commands)
    {linked : Functions.Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (caller : Lists.State) :
    ModuleBinders commands (names commands) ∧
      ∃ out, Wrapper.ReachedPrefix (Leaf.Step resolved (names commands)) 0 (enter resolved.source caller) commands out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.checked_trace profile checked caller

/-- The derived trace determines exact publication on success and returns
the first reached error with the restored caller and retained heap. -/
theorem checked_module {commands : List Command} (profile : Profile commands)
    {linked : Functions.Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (host : Catalog) (caller : Lists.State) :
    ∃ out published,
      Wrapper.ReachedPrefix (Leaf.Step resolved (names commands)) 0 (enter resolved.source caller) commands out ∧
      Leaf.Finishes (names commands) caller out published ∧
      Initializes commands host caller linked (.ok published) ∧ runModule commands host caller linked = .ok published :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.checked_module profile checked host caller

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings
