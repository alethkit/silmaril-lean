module

public import Silmaril.Languages.Python.Source.Scope.Defs
import Silmaril.Proofs.Languages.Python.Source.Scope.Thms

public section
namespace Silmaril.Languages.Python.Source

theorem enclosingBinding_eq_some_iff (name : Name) (outer : List BlockContext) (path : BlockPath) :
    enclosingBinding name outer = some path ↔ EnclosingBinding name outer path :=
  Proofs.Languages.Python.Source.Scope.enclosingBinding_eq_some_iff name outer path

theorem enclosingBinding_stops (name : Name) (parent : BlockContext) (outer : List BlockContext)
    (barrier : parent.lookupBarrier name = true) :
    enclosingBinding name (parent :: outer) = none := by
  simp [enclosingBinding, barrier]

end Silmaril.Languages.Python.Source
