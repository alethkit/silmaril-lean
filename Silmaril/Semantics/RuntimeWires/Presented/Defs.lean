module

public import Silmaril.Semantics.RuntimeWires.Presentation.Defs
public import Mathlib.CategoryTheory.Monoidal.Category

@[expose] public section

namespace Silmaril.RuntimeWires.Diagram

open CategoryTheory

universe u v

/-- Objects of the category presented by a signature and its equations. -/
structure Presented {O : Type u} (S : Signature.{u,v} O) (E : Equations S) where
  word : List O

namespace Presented

variable {O : Type u} {S : Signature.{u,v} O} {E : Equations S}

instance : Category.{max u v} (Presented S E) where
  Hom A B := Hom S E A.word B.word
  id A := Quotient.mk'' (Diagram.id A.word)
  comp := Quotient.map₂ Diagram.comp (fun _ _ hf _ _ hg => Congruence.comp hf hg)
  id_comp f := Quotient.inductionOn f fun f => Quotient.sound (Congruence.id_comp f)
  comp_id f := Quotient.inductionOn f fun f => Quotient.sound (Congruence.comp_id f)
  assoc f g h :=
    Quotient.inductionOn₃ f g h fun f g h => Quotient.sound (Congruence.comp_assoc f g h)

/-- Regard a presentation term as a categorical morphism. -/
def ofTerm {A B : Presented S E} (f : Diagram S A.word B.word) : A ⟶ B := Quotient.mk'' f

/-- Tensor objects by concatenating boundary words. -/
def concat (A B : Presented S E) : Presented S E := ⟨A.word ++ B.word⟩

/-- Tensor quotient morphisms using the term tensor. -/
def tensorMap {A B C D : Presented S E} (f : A ⟶ B) (g : C ⟶ D) : concat A C ⟶ concat B D :=
  Quotient.map₂ Diagram.tensor (fun _ _ hf _ _ hg => Congruence.tensor hf hg) f g

/-- The empty word. -/
def empty : Presented S E := ⟨[]⟩

theorem concat_assoc (A B C : Presented S E) :
    concat (concat A B) C = concat A (concat B C) :=
  congrArg Presented.mk (List.append_assoc _ _ _)

theorem empty_concat (A : Presented S E) : concat empty A = A :=
  congrArg Presented.mk (List.nil_append _)

theorem concat_empty (A : Presented S E) : concat A empty = A :=
  congrArg Presented.mk (List.append_nil _)

/-- The structural isomorphisms are identities transported along equalities of words. -/
instance : MonoidalCategoryStruct (Presented S E) where
  tensorObj := concat
  whiskerLeft A {_ _} f := tensorMap (𝟙 A) f
  whiskerRight f A := tensorMap f (𝟙 A)
  tensorHom := tensorMap
  tensorUnit := empty
  associator A B C := eqToIso (concat_assoc A B C)
  leftUnitor A := eqToIso (empty_concat A)
  rightUnitor A := eqToIso (concat_empty A)

end Presented

end Silmaril.RuntimeWires.Diagram

namespace Silmaril.RuntimeWires.Presentation

universe u v

/-- The objects and category of the runtime presentation. -/
abbrev Runtime (G : EffectfulPolygraph.{u,v}) := Diagram.Presented (signature G) (Relations G)

end Silmaril.RuntimeWires.Presentation
