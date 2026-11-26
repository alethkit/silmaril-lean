module

public import Silmaril.Semantics.Categories.Thms
public import Silmaril.Semantics.ITree.Trace.Thms

/-! # The weak-tree Kleisli category and its hom orders -/

@[expose] public section

namespace Silmaril.Elgot.ITree

open CategoryTheory

universe u

/-- The ordinary Type–Kleisli category of the existing weak-tree monad, at
the first universe containing its observations. -/
abbrev WeakKleisli (E : Type u → Type u) :=
  CategoryTheory.Kleisli (CategoryTheory.Kleisli.Type.TM (Tree E :
    Type (u + 1) → Type (u + 1)))

namespace WeakKleisli

variable {E : Type u → Type u}

/-- Compare arrows by finite trace inclusion at each common input. -/
scoped instance homPartialOrder (X Y : WeakKleisli E) : PartialOrder (X ⟶ Y) where
  le f g := ∀ x : X.of, TraceLE.{u, u + 1} (f.of x) (g.of x)
  le_refl f x := TraceLE.refl (f.of x)
  le_trans _ _ _ hfg hgh x := (hfg x).trans (hgh x)
  le_antisymm _ _ hfg hgf := Kleisli.hom_ext (ConcreteCategory.coe_ext
    (funext fun x => (hfg x).antisymm (hgf x)))

end WeakKleisli
end Silmaril.Elgot.ITree
