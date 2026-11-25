module

public import Silmaril.Semantics.RuntimeWires.Presented.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.Presented.Monoidal

@[expose] public section

namespace Silmaril.RuntimeWires.Diagram.Presented

open CategoryTheory

universe u v

/-- Strict tensor laws on words induce a monoidal category on the quotient.
In particular, the runtime presentation in Definition 3.8 is monoidal. -/
instance instMonoidalCategory {O : Type u} {S : Signature.{u,v} O} {E : Equations S} :
    MonoidalCategory (Presented S E) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by exact Proofs.id_tensorMap_id)
    (id_tensorHom := fun _ {_ _} _ => rfl)
    (tensorHom_id := fun {_ _} _ _ => rfl)
    (tensorHom_comp_tensorHom := by intros; apply Proofs.tensorMap_comp)
    (associator_naturality := by intros; apply Proofs.associator_naturality)
    (leftUnitor_naturality := by intros; apply Proofs.leftUnitor_naturality)
    (rightUnitor_naturality := by intros; apply Proofs.rightUnitor_naturality)
    (pentagon := by exact Proofs.pentagon)
    (triangle := by exact Proofs.triangle)

end Silmaril.RuntimeWires.Diagram.Presented
