module

public import Silmaril.Languages.Starlark.Modules.Resolve.Defs
public import Silmaril.Languages.Starlark.Modules.Operational.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve

/-- Checked elaboration followed by the independent resolved module rules. -/
inductive Initializes (commands : List Command) (host : Catalog) (caller : Lists.State)
    (linked : Functions.Program) : Result → Prop where
  | reject {error : Error} : resolve commands linked = .error error →
      Initializes commands host caller linked (.error error)
  | run {resolved : ResolvedModule} {out : Modules.Result Published} :
      resolve commands linked = .ok resolved →
      Modules.Initializes resolved.program host resolved.source caller out →
      Initializes commands host caller linked (.ok out)

end Silmaril.Languages.Starlark.Modules.Resolve
