module

public import Silmaril.Logic.Temporal.TLA.General.Institution.Defs

public section

namespace Silmaril.Logic.Temporal.TLA.General.Institution

open CategoryTheory

universe u

variable {Sorts : Type u} {Value : Sorts → Type u} {Γ Δ : Scope Sorts}

/-- A translated General TLA sentence holds in the target room exactly when
the original holds on the reduct in the source room. -/
theorem satisfaction (f : Γ ⟶ Δ) (M : Model Value Δ) (p : Formula Value Γ) :
    ((roomFunctor Value).obj Δ).Sat M (((roomFunctor Value).map f).sen p) ↔
      p.Satisfies (M.reduct f.val) :=
  ((roomFunctor Value).map f).sat M p

end Silmaril.Logic.Temporal.TLA.General.Institution
