module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Module

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace

open Block (ModuleBinders)

/-- Accepted normalized syntax in the profile supplies the source trace
from actual module entry, including any first reached error. -/
theorem checked_trace {chain : Forwarding.Chain} {after : List Command} (profile : Profile chain after)
    {linked : Functions.Program} {resolved : ResolvedModule}
    (checked : resolve (root chain :: after) linked = .ok resolved) (caller : Lists.State) :
    let commands := root chain :: after
    let globals := names commands
    ModuleBinders commands globals ∧
      ∃ out, Wrapper.ReachedPrefix (Leaf.Step resolved globals) 0 (enter resolved.source caller) commands out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.checked_trace profile checked caller

/-- The trace and its publication or failure observation both exist. The
observation gives the exact resolved operational and denotational results. -/
theorem checked_source_module {chain : Forwarding.Chain} {after : List Command} (profile : Profile chain after)
    {linked : Functions.Program} {resolved : ResolvedModule}
    (checked : resolve (root chain :: after) linked = .ok resolved) (host : Catalog) (caller : Lists.State) :
    let commands := root chain :: after
    let globals := names commands
    ∃ out published,
      Wrapper.ReachedPrefix (Leaf.Step resolved globals) 0 (enter resolved.source caller) commands out ∧
      Leaf.Finishes globals caller out published ∧
      Initializes commands host caller linked (.ok published) ∧ runModule commands host caller linked = .ok published :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.checked_source_module profile checked host caller

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
