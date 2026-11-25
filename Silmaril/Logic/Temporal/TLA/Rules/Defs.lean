module

public import Silmaril.Logic.Temporal.TLA.General.Defs

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.General.Scope.Rename
universe u

variable {Sorts : Type u}

/-- Include the outer names in a scope extended by one flexible name. -/
def weakenFlex (Γ : Scope Sorts) (a : Sorts) : Rename Γ (Γ.bindFlex a) :=
  ⟨Context.Rename.id _, fun _ x => Context.old x⟩

/-- Include the outer names in a scope extended by one rigid name. -/
def weakenRigid (Γ : Scope Sorts) (a : Sorts) : Rename Γ (Γ.bindRigid a) :=
  ⟨fun _ x => Context.old x, Context.Rename.id _⟩

end Silmaril.Logic.Temporal.TLA.General.Scope.Rename
