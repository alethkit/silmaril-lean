module

public import Silmaril.Languages.Python.Source.Scope.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Source.Scope

open Silmaril.Languages.Python.Source

theorem enclosingBinding_eq_some_iff (name : Name) (outer : List BlockContext) (path : BlockPath) :
    enclosingBinding name outer = some path ↔ EnclosingBinding name outer path := by
  induction outer with
  | nil =>
    constructor
    · simp [enclosingBinding]
    · intro found
      cases found
  | cons block outer ih =>
    constructor
    · intro result
      cases barrier : block.lookupBarrier name with
      | true => simp [enclosingBinding, barrier] at result
      | false =>
        cases binds : block.binds name with
        | true =>
          have equal : block.path = path := by simpa [enclosingBinding, barrier, binds] using result
          rw [← equal]
          exact .nearest barrier binds
        | false =>
          exact .outside barrier binds (ih.mp (by simpa [enclosingBinding, barrier, binds] using result))
    · intro found
      cases found with
      | nearest barrier binds => simp [enclosingBinding, barrier, binds]
      | outside barrier binds found => simpa [enclosingBinding, barrier, binds] using ih.mpr found

end Silmaril.Proofs.Languages.Python.Source.Scope
