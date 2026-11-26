module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Execution

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published

open Functions (Program)
open Lists (State)

/-- A checked load-free plan derives its reached source trace from module
entry. The same trace determines exact initialization and publication. -/
theorem module_agrees {commands : List Resolve.Command}
    {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (checked : resolve commands linked = .ok resolved) (host : Catalog) (caller : State) :
    ∃ reached, ExecutesAll (Trace.names commands) (enter resolved.source caller) commands reached ∧
      Modules.Runs resolved.program host (enter resolved.source caller) resolved.source.commands reached ∧
      Modules.Initializes resolved.program host resolved.source caller (finish resolved.source caller reached) ∧
      runModule commands host caller linked = .ok (finish resolved.source caller reached) ∧
      ∀ published finished, finish resolved.source caller reached = .ok published finished →
        PublishedLive exports resolved.program published finished :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.module_agrees
    profile checked host caller

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
