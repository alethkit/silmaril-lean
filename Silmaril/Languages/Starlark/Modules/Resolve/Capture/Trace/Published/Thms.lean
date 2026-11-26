module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Execution

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published

open Functions (Program)
open Defaults.Nested.Sequence.Recursive.Call (BodyEntry)
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

/-- Module execution keeps the caller's original cells, allowing
publication to change only their frozen flags. -/
theorem module_agrees_preserving {commands : List Resolve.Command}
    {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (checked : resolve commands linked = .ok resolved) (host : Catalog) (caller : State) :
    ∃ reached, ExecutesAll (Trace.names commands) (enter resolved.source caller) commands reached ∧
      Modules.Runs resolved.program host (enter resolved.source caller) resolved.source.commands reached ∧
      Modules.Initializes resolved.program host resolved.source caller (finish resolved.source caller reached) ∧
      runModule commands host caller linked = .ok (finish resolved.source caller reached) ∧
      KeepsContents caller (resultState (finish resolved.source caller reached)) ∧
      ∀ published finished, finish resolved.source caller reached = .ok published finished →
        PublishedLive exports resolved.program published finished :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.module_agrees_preserving
    profile checked host caller

theorem plan_globals {commands : List Resolve.Command}
    {env exports : Environment} {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule}
    (profile : Plan (Trace.names commands) env commands linked code final exports)
    (checked : resolve commands linked = .ok resolved) :
    resolved.source.globals = Trace.names commands :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.plan_globals profile checked

theorem plan_code {commands : List Resolve.Command}
    {env exports : Environment} {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule}
    (profile : Plan (Trace.names commands) env commands linked code final exports)
    (checked : resolve commands linked = .ok resolved) :
    resolved.source.commands = code ∧ resolved.program = final :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.plan_code profile checked

/-- A linked callable activates its independently checked body using the
reached defaults and installed capture cells. -/
theorem enter_callable {callee : Callable}
    {commands : List Resolve.Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (known : callee.Linked resolved.program) :
    BodyEntry callee.site resolved.program (List.range resolved.program.size) callee.id callee.BodyRuns :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.enter_callable checked known

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
