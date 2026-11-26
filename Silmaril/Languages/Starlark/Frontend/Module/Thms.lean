module

public import Silmaril.Languages.Starlark.Frontend.Module.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Thms
import Silmaril.Proofs.Languages.Starlark.Frontend.Module.CallArguments

public section

namespace Silmaril.Languages.Starlark.Frontend.Module

/-- Existing module agreement applies to the normalized commands produced by the frontend. -/
theorem initializes_iff_run (parsed : ParsedModule) (out : Modules.Resolve.Result) :
    Modules.Resolve.Initializes parsed.toCommands (fun _ => none) {} #[] out ↔ parsed.run = out :=
  Modules.Resolve.initializes_iff_runModule parsed.toCommands (fun _ => none) {} #[] out

/-- Successful lowering preserves explicit keyword names in source order,
including any repetitions for normalized validation. -/
theorem lowerNamedArguments_names {arguments : List LocatedNamedArgument}
    {lowered : List (String × Functions.Lowering.Resolve.SourceExpr)}
    (lowering : lowerNamedArguments arguments = .ok lowered) :
    lowered.map Prod.fst = arguments.map LocatedNamedArgument.name :=
  Silmaril.Proofs.Languages.Starlark.Frontend.Module.lowerNamedArguments_names lowering

end Silmaril.Languages.Starlark.Frontend.Module
