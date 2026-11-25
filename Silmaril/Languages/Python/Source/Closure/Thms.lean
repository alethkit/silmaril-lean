module

public import Silmaril.Languages.Python.Source.Closure.Defs
import Silmaril.Proofs.Languages.Python.Source.Closure.Thms

public section
namespace Silmaril.Languages.Python.Source.Closure

theorem slot_iff (parent : Scope) (capture : Capture) :
    (Slot.find? parent capture).isSome ↔ Available parent capture :=
  Proofs.Languages.Python.Source.Closure.slot_iff parent capture

theorem layout_iff (parent : Scope) (captures : List Capture) :
    (layout? parent captures).isSome ↔ ∀ capture ∈ captures, Available parent capture :=
  Proofs.Languages.Python.Source.Closure.layout_iff parent captures

end Silmaril.Languages.Python.Source.Closure
