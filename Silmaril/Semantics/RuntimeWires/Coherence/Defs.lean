module

public import Silmaril.Semantics.Categories.Thms
public import Silmaril.Semantics.RuntimeWires.Computations.Defs

@[expose] public section

/-!
# Premonoidal coherence of the runtime construction

Lemma 3.11 (pp. 9:9–9:10) of Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.Presentation.Computations

open CategoryTheory
open scoped MonoidalCategory

universe u v

variable {G : EffectfulPolygraph.{u,v}}

/-- The empty value word. Its computation boundary still has one runtime wire. -/
def empty : Computations G := ⟨[]⟩

theorem concat_assoc (A B C : Computations G) :
    concat (concat A B) C = concat A (concat B C) :=
  congrArg Computations.mk (List.append_assoc _ _ _)

theorem empty_concat (A : Computations G) : concat empty A = A :=
  congrArg Computations.mk (List.nil_append _)

theorem concat_empty (A : Computations G) : concat A empty = A :=
  congrArg Computations.mk (List.append_nil _)

/-- The coherence maps are identities transported along the corresponding word equalities. -/
instance monoidalData : MonoidalCategoryStruct (Computations G) where
  tensorObj := concat
  whiskerLeft A {_ _} f := (whiskerLeft A).map f
  whiskerRight f A := (whiskerRight A).map f
  tensorUnit := empty
  associator A B C := eqToIso (concat_assoc A B C)
  leftUnitor A := eqToIso (empty_concat A)
  rightUnitor A := eqToIso (concat_empty A)

end Silmaril.RuntimeWires.Presentation.Computations
