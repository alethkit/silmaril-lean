module

public import Silmaril.Semantics.Page.Trace.Defs
public import Silmaril.Semantics.Operational.Determinism.Defs

/-! Page access traces as labelled paths in the generic operational API. -/

@[expose] public section
namespace Silmaril.Semantics.Page

universe u v w
variable {Id : Type u} {Content : Type v} {Memory : Type w}

/-- Every accepted access is visible. Any state can end a finite observation. -/
def Access.labelled (access : Access Id Content Memory) :
    Operational.Labelled Memory (AccessEvent Id Content) Unit where
  step initial event final := match event with
    | none => False
    | some (.read page value) => access.read initial page = some value ∧ initial = final
    | some (.write page value) => access.write initial page value = some final
  observe _ result := result = .returned ()

end Silmaril.Semantics.Page
