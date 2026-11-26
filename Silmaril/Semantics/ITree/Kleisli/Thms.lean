module

public import Silmaril.Semantics.ITree.Kleisli.Defs
import Silmaril.Proofs.Semantics.ITree.Kleisli.Order

/-! # Monotone composition and iteration in weak-tree Kleisli homs -/

public section

namespace Silmaril.Elgot.ITree.WeakKleisli

open CategoryTheory CategoryTheory.Limits

universe u

variable {E : Type u → Type u}

/-- Kleisli composition preserves the hom order in both arguments. -/
theorem comp_mono {X Y Z : WeakKleisli E} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    (hf : f ≤ f') (hg : g ≤ g') : f ≫ g ≤ f' ≫ g' :=
  Silmaril.Proofs.Semantics.Elgot.ITree.WeakKleisli.comp_mono hf hg

/-- The existing categorical iterator preserves the hom order. -/
theorem iterate_mono {X Y : WeakKleisli E} {f g : X ⟶ Y ⨿ X} (h : f ≤ g) :
    CategoryTheory.iterate f ≤ CategoryTheory.iterate g :=
  Silmaril.Proofs.Semantics.Elgot.ITree.WeakKleisli.iterate_mono h

end Silmaril.Elgot.ITree.WeakKleisli
