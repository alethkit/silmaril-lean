module

public import Silmaril.Semantics.RuntimeWires.Braiding.Thms

@[expose] public section

/-!
# Computations with a single runtime wire

The underlying category and whiskering functors used in Lemma 3.11 of
Román and Sobociński, *String Diagrams for Premonoidal Categories*.
Morphisms are represented at the leftmost runtime position.
-/

namespace Silmaril.RuntimeWires.Presentation

open CategoryTheory
open scoped MonoidalCategory

universe u v

/-- The objects are value-word boundaries. Their morphisms use one runtime wire. -/
structure Computations (G : EffectfulPolygraph.{u,v}) where
  word : List G.Obj

namespace Computations

variable {G : EffectfulPolygraph.{u,v}}

/-- Place the runtime to the left of the value word. -/
def boundary (A : Computations G) : Runtime G := runtime G ⊗ valueWord A.word

instance : Category.{max u v} (Computations G) where
  Hom A B := A.boundary ⟶ B.boundary
  id A := 𝟙 A.boundary
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- View the chosen leftmost component as its arrow in the runtime category. -/
def inRuntime (G : EffectfulPolygraph.{u,v}) : Computations G ⥤ Runtime G where
  obj := boundary
  map f := f

/-- Recover the coherent family of components from a leftmost computation. -/
noncomputable def cliqueHom {A B : Computations G} (f : A ⟶ B) :
    Clique.Hom (braidClique A.word) (braidClique B.word) :=
  (leftmostEquiv A.word B.word).symm f

theorem cliqueHom_leftmost {A B : Computations G} (f : A ⟶ B) :
    (cliqueHom f).app 0 0 = f :=
  (leftmostEquiv_apply (cliqueHom f)).symm.trans ((leftmostEquiv A.word B.word).apply_symm_apply f)

/-- The runtime input and output of an effect are both on the left. -/
def effect (e : G.effect.Edge) :
    (⟨G.effect.source e⟩ : Computations G) ⟶ ⟨G.effect.target e⟩ :=
  Diagram.Presented.ofTerm (Diagram.gen (S := signature G) (.effect e))

/-- Tensor objects by concatenating the value words. -/
def concat (A B : Computations G) : Computations G :=
  ⟨A.word ++ B.word⟩

/-- Separate the value words while keeping the runtime on the left. -/
def splitRight (A B : Computations G) :
    (concat A B).boundary ≅ A.boundary ⊗ valueWord B.word :=
  eqToIso (congrArg ((runtime G) ⊗ ·) (word_eq A B)) ≪≫
    (α_ (runtime G) (valueWord A.word) (valueWord B.word)).symm
where
  word_eq (A B : Computations G) :
      valueWord (G := G) (A.word ++ B.word) = valueWord A.word ⊗ valueWord B.word :=
    congrArg Diagram.Presented.mk (List.map_append ..)

/-- Split the value words and braid the runtime past the first word. -/
def splitLeft (A B : Computations G) :
    (concat A B).boundary ≅ valueWord A.word ⊗ B.boundary :=
  splitRight A B ≪≫ (crossingWord A.word ⊗ᵢ Iso.refl (valueWord B.word)) ≪≫
    α_ (valueWord A.word) (runtime G) (valueWord B.word)

/-- Transport an endofunctor along the chosen representations of value words. -/
def whisker (obj : Computations G → Computations G) (F : Runtime G ⥤ Runtime G)
    (split : ∀ A, (obj A).boundary ≅ F.obj A.boundary) : Computations G ⥤ Computations G where
  obj := obj
  map {A B} f := show (obj A).boundary ⟶ (obj B).boundary from
    (split A).hom ≫ F.map (show A.boundary ⟶ B.boundary from f) ≫ (split B).inv
  map_id A := by
    change (split A).hom ≫ F.map (𝟙 A.boundary) ≫ (split A).inv = 𝟙 (obj A).boundary
    simp
  map_comp {A B C} f g := by
    change A.boundary ⟶ B.boundary at f
    change B.boundary ⟶ C.boundary at g
    change (split A).hom ≫ F.map (f ≫ g) ≫ (split C).inv =
      ((split A).hom ≫ F.map f ≫ (split B).inv) ≫ ((split B).hom ≫ F.map g ≫ (split C).inv)
    simp [Category.assoc]

/-- Right whiskering tensors by a fixed identity on value wires. -/
def whiskerRight (B : Computations G) : Computations G ⥤ Computations G :=
  whisker (concat · B) (MonoidalCategory.tensorRight (valueWord B.word)) (splitRight · B)

/-- Left whiskering braids the runtime to the computation and back. -/
def whiskerLeft (A : Computations G) : Computations G ⥤ Computations G :=
  whisker (concat A) (MonoidalCategory.tensorLeft (valueWord A.word)) (splitLeft A)

end Computations

end Silmaril.RuntimeWires.Presentation
