module

public import Silmaril.Semantics.RuntimeWires.Presented.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.Presented.Monoidal
import Silmaril.Proofs.Semantics.RuntimeWires.Presented.Equations

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

variable {O : Type u} {S : Signature.{u,v} O} {E F : Equations S}

/-- Keep the same typed terms and impose the additional presentation equations. -/
def imposeEquations (includeEquation : ∀ {A B} {f g : Diagram S A B}, E f g → F f g) :
    Presented S E ⥤ Presented S F where
  obj X := ⟨X.word⟩
  map {A B} f := Quotient.map (fun t : Diagram S A.word B.word => t)
    (fun _ _ h => by exact Proofs.includeCongruence includeEquation h) f
  map_id _ := rfl
  map_comp f g := by
    exact Quotient.inductionOn₂ f g (fun _ _ => rfl)

theorem imposeEquations_ofTerm (includeEquation : ∀ {A B} {f g : Diagram S A B}, E f g → F f g)
    {A B : Presented S E} (f : Diagram S A.word B.word) :
    (imposeEquations includeEquation).map (ofTerm f) =
      ofTerm (A := ⟨A.word⟩) (B := ⟨B.word⟩) (E := F) f := by rfl

end Silmaril.RuntimeWires.Diagram.Presented
