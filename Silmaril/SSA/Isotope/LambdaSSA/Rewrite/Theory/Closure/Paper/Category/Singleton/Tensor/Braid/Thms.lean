module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Braid.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WhiskerBraid

/-! # Swapping the active and fixed factors of a whiskering -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory
open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

@[simp] theorem braid_braid (A B : τ) : braid (Φ := Φ) A B ≫ braid B A = 𝟙 (ofType (product A B)) :=
  WhiskerBraid.braid_braid A B

/-- The guarded swap is an involutive isomorphism. -/
@[expose] def braidIso (A B : τ) :
    ofType (Φ := Φ) (product A B) ≅ ofType (product B A) where
  hom := braid A B
  inv := braid B A
  hom_inv_id := braid_braid A B
  inv_hom_id := braid_braid B A

theorem whiskerRight_braid {A B : τ} (X : τ) (f : ofType (Φ := Φ) A ⟶ ofType B) :
    whiskerRight f (ofType X) ≫ braid B X = braid A X ≫ whiskerLeft (ofType X) f :=
  WhiskerBraid.whiskerRight_braid X f

theorem whiskerLeft_braid {A B : τ} (X : τ) (f : ofType (Φ := Φ) A ⟶ ofType B) :
    whiskerLeft (ofType X) f ≫ braid X B = braid X A ≫ whiskerRight f (ofType X) := by
  apply (cancel_mono (braidIso (Φ := Φ) B X).hom).mp
  change (whiskerLeft (ofType X) f ≫ braid X B) ≫ braid B X =
    (braid X A ≫ whiskerRight f (ofType X)) ≫ braid B X
  erw [Category.assoc, braid_braid, Category.comp_id, Category.assoc, whiskerRight_braid X f,
    ← Category.assoc (braid X A), braid_braid, Category.id_comp]

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
