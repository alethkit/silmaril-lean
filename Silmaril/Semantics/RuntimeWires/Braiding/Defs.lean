module

public import Silmaril.Semantics.RuntimeWires.Presented.Thms
public import Silmaril.Semantics.RuntimeWires.Clique.Thms

@[expose] public section

/-!
# Runtime braid cliques

Definitions 3.9 and 3.10 of Román and Sobociński,
*String Diagrams for Premonoidal Categories*.
-/

namespace Silmaril.RuntimeWires.Presentation

open CategoryTheory
open scoped MonoidalCategory

universe u v

variable {G : EffectfulPolygraph.{u,v}}

/-- The word consisting of a single runtime wire. -/
def runtime (G : EffectfulPolygraph.{u,v}) : Runtime G := ⟨[none]⟩

/-- Regard a list of value sorts as a runtime boundary. -/
def valueWord (A : List G.Obj) : Runtime G := ⟨values A⟩

/-- The runtime crosses each value sort by an invertible generator. -/
def crossing (x : G.Obj) : runtime G ⊗ valueWord [x] ≅ valueWord [x] ⊗ runtime G where
  hom := Diagram.Presented.ofTerm (crossRight (G := G) x)
  inv := Diagram.Presented.ofTerm (crossLeft (G := G) x)
  hom_inv_id := Quotient.sound (.equation (.cancelRight x))
  inv_hom_id := Quotient.sound (.equation (.cancelLeft x))

/-- The runtime crosses a word by successively crossing its letters. -/
def crossingWord :
    (A : List G.Obj) → runtime G ⊗ valueWord A ≅ valueWord A ⊗ runtime G
  | [] => ρ_ (runtime G) ≪≫ (λ_ (runtime G)).symm
  | x :: A =>
      (α_ (runtime G) (valueWord [x]) (valueWord A)).symm ≪≫
        (crossing x ⊗ᵢ Iso.refl (valueWord A)) ≪≫
        α_ (valueWord [x]) (runtime G) (valueWord A) ≪≫
        (Iso.refl (valueWord [x]) ⊗ᵢ crossingWord A) ≪≫
        (α_ (valueWord [x]) (valueWord A) (runtime G)).symm

/-- The positions at which one can insert the runtime in the value word. -/
abbrev Position (A : List G.Obj) := Fin (A.length + 1)

/-- The runtime after the first `i` value wires. -/
def placed (A : List G.Obj) (i : Position A) : Runtime G :=
  (valueWord (A.take i) ⊗ runtime G) ⊗ valueWord (A.drop i)

/-- Splitting a word does not change its boundary. -/
theorem valueWord_split (A : List G.Obj) (n : Nat) :
    valueWord A = valueWord (A.take n) ⊗ valueWord (A.drop n) := by
  change Diagram.Presented.mk (values A) =
    Diagram.Presented.mk (values (A.take n) ++ values (A.drop n))
  rw [← List.map_append, List.take_append_drop]

/-- Move the leftmost runtime to the given position. -/
def placeIso (A : List G.Obj) (i : Position A) :
    runtime G ⊗ valueWord A ≅ placed A i :=
  eqToIso (congrArg ((runtime G) ⊗ ·) (valueWord_split A i)) ≪≫
    (α_ (runtime G) (valueWord (A.take i)) (valueWord (A.drop i))).symm ≪≫
    (crossingWord (A.take i) ⊗ᵢ Iso.refl (valueWord (A.drop i)))

/-- Definition 3.9, with the runtime appearing once at every possible position. -/
def braidClique (A : List G.Obj) : Clique (Runtime G) (Position A) :=
  Clique.ofIsoFamily (placed A) (placeIso A)

end Silmaril.RuntimeWires.Presentation
