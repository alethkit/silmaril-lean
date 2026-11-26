module

public import Silmaril.Semantics.ITree.Kleisli.Defs

public section

namespace Silmaril.Proofs.Semantics.Elgot.ITree.WeakKleisli

open CategoryTheory CategoryTheory.Limits
open Silmaril.Elgot.ITree
open scoped Silmaril.Elgot.ITree.WeakKleisli

universe u

variable {E : Type u → Type u}

theorem comp_mono {X Y Z : WeakKleisli E} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    (hf : f ≤ f') (hg : g ≤ g') : f ≫ g ≤ f' ≫ g' := by
  intro x
  rw [Kleisli.Type.comp_of_eq_kleisliRight, Kleisli.Type.comp_of_eq_kleisliRight]
  exact TraceLE.bind (hf x) hg

theorem iterate_mono {X Y : WeakKleisli E} {f g : X ⟶ Y ⨿ X} (h : f ≤ g) :
    CategoryTheory.iterate f ≤ CategoryTheory.iterate g := by
  intro x
  rw [Kleisli.Type.iterate_of, Kleisli.Type.iterate_of]
  exact TraceLE.iter (comp_mono h le_rfl) x

end Silmaril.Proofs.Semantics.Elgot.ITree.WeakKleisli
