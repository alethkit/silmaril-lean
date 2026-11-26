module

public import Silmaril.Languages.Starlark.Frontend.Module.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Thms

public section

namespace Silmaril.Languages.Starlark.Frontend.Module

/-- Existing module agreement applies to the normalized commands produced by the frontend. -/
theorem initializes_iff_run (parsed : ParsedModule) (out : Modules.Resolve.Result) :
    Modules.Resolve.Initializes parsed.toCommands (fun _ => none) {} #[] out ↔ parsed.run = out :=
  Modules.Resolve.initializes_iff_runModule parsed.toCommands (fun _ => none) {} #[] out

end Silmaril.Languages.Starlark.Frontend.Module
