module

public import Mathlib.CategoryTheory.EqToHom

@[expose] public section

/-!
# Cliques of isomorphisms

The categorical construction behind Definitions 3.9 and 3.10 of Román and
Sobociński, *String Diagrams for Premonoidal Categories*.
-/

namespace Silmaril.RuntimeWires

open CategoryTheory

universe u v w

/-- A family of objects with a coherent isomorphism between every pair. In
Definition 3.9 the indices are the positions of a distinguished runtime wire. -/
structure Clique (C : Type u) [Category.{v} C] (I : Type w) where
  obj : I → C
  braid : (i j : I) → obj i ≅ obj j
  braid_id (i : I) : (braid i i).hom = 𝟙 (obj i)
  braid_comp (i j k : I) : (braid i j).hom ≫ (braid j k).hom = (braid i k).hom

namespace Clique

variable {C : Type u} [Category.{v} C]

/-- A clique morphism as in Definition 3.10. Both endpoints may be reindexed. -/
structure Hom {I J : Type w} (A : Clique C I) (B : Clique C J) where
  app : (i : I) → (j : J) → A.obj i ⟶ B.obj j
  naturality (i i' : I) (j j' : J) :
    app i j ≫ (B.braid j j').hom = (A.braid i i').hom ≫ app i' j'

/-- Transport coherence through isomorphisms from a common base object. -/
def ofIsoFamily {I : Type w} {base : C} (obj : I → C)
    (fromBase : ∀ i, base ≅ obj i) : Clique C I where
  obj := obj
  braid i j := (fromBase i).symm ≪≫ fromBase j
  braid_id i := (fromBase i).inv_hom_id
  braid_comp i j k := by simp [Category.assoc]

end Clique

end Silmaril.RuntimeWires
