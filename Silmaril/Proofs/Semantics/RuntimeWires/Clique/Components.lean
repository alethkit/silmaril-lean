module

public import Silmaril.Semantics.RuntimeWires.Clique.Defs

public section

namespace Silmaril.RuntimeWires.Proofs

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] {I J : Type w} {A : Clique C I} {B : Clique C J}

private theorem hom_ext {f g : Clique.Hom A B}
    (h : ∀ i j, f.app i j = g.app i j) : f = g := by
  have h' : f.app = g.app := funext fun i => funext (h i)
  cases f
  cases g
  cases h'
  rfl

private def ofComponent (a : I) (b : J) (f : A.obj a ⟶ B.obj b) : Clique.Hom A B where
  app i j := (A.braid i a).hom ≫ f ≫ (B.braid b j).hom
  naturality i i' j j' := by
    simp only [Category.assoc, B.braid_comp]
    rw [← Category.assoc (A.braid i i').hom, A.braid_comp]

def cliqueComponentEquiv (a : I) (b : J) : Clique.Hom A B ≃ (A.obj a ⟶ B.obj b) where
  toFun f := f.app a b
  invFun := ofComponent a b
  left_inv f := hom_ext fun i j => by
    change (A.braid i a).hom ≫ f.app a b ≫ (B.braid b j).hom = f.app i j
    have ht := f.naturality a a b j
    have hs := f.naturality i a j j
    rw [A.braid_id, Category.id_comp] at ht
    rw [B.braid_id, Category.comp_id] at hs
    rw [ht, ← hs]
  right_inv f := by
    change (A.braid a a).hom ≫ f ≫ (B.braid b b).hom = f
    rw [A.braid_id, B.braid_id, Category.id_comp, Category.comp_id]

end Silmaril.RuntimeWires.Proofs
