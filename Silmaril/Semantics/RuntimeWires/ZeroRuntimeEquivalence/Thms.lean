module

public import Silmaril.Semantics.RuntimeWires.ZeroRuntimeEquivalence.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ZeroRuntimeEquivalence.Faithful

@[expose] public section

namespace Silmaril.RuntimeWires.Presentation

open CategoryTheory

universe u v

variable {G : EffectfulPolygraph.{u,v}}

/-- Erasing the runtime syntax recovers the original pure quotient arrow. -/
theorem eraseValueMorphism_map {A B : Pure G} (f : A ⟶ B) :
    eraseValueMorphism ((pureValues G).map f) = f :=
  Proofs.ZeroRuntimeEquivalence.erase_section f

/-- The pure quotient arrows correspond bijectively to the zero-runtime arrows.
Erasure supplies the inverse to the pure-value interpretation. -/
def zeroRuntimeHomEquiv (A B : Pure G) :
    (A ⟶ B) ≃ ((pureValues G).obj A ⟶ (pureValues G).obj B) where
  toFun := (pureValues G).map
  invFun := eraseValueMorphism
  left_inv := eraseValueMorphism_map
  right_inv f := by
    obtain ⟨p, rfl⟩ := pureValues_surjective f
    exact congrArg ((pureValues G).map) (eraseValueMorphism_map p)

instance pureValues_faithful : (pureValues G).Faithful where
  map_injective e := (zeroRuntimeHomEquiv _ _).injective e

end Silmaril.RuntimeWires.Presentation
