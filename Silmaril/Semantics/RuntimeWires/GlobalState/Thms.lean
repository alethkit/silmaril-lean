module

public import Silmaril.Semantics.RuntimeWires.GlobalState.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.GlobalState.Races

public section

namespace Silmaril.RuntimeWires.GlobalState

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {R X : C} [ComonObj X] (S : GlobalState R X)

/-- Proposition 4.3, overlapping case. The overwritten transformation must
be discardable. Instantiating in the two orders gives the two lost updates. -/
theorem race_last {f : X ⟶ X} (hf : Discardable f) (g : X ⟶ X) :
    S.race f g = S.update g :=
  Proofs.race_last S hf g

/-- Proposition 4.3, serial case. Instantiating in the two orders gives the
two compositions. Serial execution does not require discardability. -/
theorem update_comp (f g : X ⟶ X) :
    S.update f ≫ S.update g = S.update (f ≫ g) :=
  Proofs.update_comp S f g

end Silmaril.RuntimeWires.GlobalState
