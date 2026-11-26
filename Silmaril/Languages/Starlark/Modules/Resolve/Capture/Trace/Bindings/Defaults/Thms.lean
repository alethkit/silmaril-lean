module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Thms
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Module

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults

open Block (ModuleBinders)

/-- Checked module entry derives a reached trace for interleaved required
and defaulted calls. The schedule supplies source provenance. Execution
supplies the actual closure addresses and their saved values. -/
theorem checked_trace {commands : List Command} (profile : Profile commands)
    {linked : Functions.Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (caller : Lists.State) :
    ModuleBinders commands (names commands) ∧
      ∃ out, Wrapper.ReachedPrefix (Step resolved (names commands)) 0 (enter resolved.source caller) commands out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults.checked_trace profile checked caller

/-- Independent source execution agrees with operational initialization and
the module denotation on publication or the first reached error, including
caller restoration and the exact shared heap. -/
theorem checked_module {commands : List Command} (profile : Profile commands)
    {linked : Functions.Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (host : Catalog) (caller : Lists.State) :
    ∃ out publication,
      Wrapper.ReachedPrefix (Step resolved (names commands)) 0 (enter resolved.source caller) commands out ∧
      Leaf.Finishes (names commands) caller out publication ∧
      Initializes commands host caller linked (.ok publication) ∧ runModule commands host caller linked = .ok publication :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults.checked_module profile checked host caller

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults
