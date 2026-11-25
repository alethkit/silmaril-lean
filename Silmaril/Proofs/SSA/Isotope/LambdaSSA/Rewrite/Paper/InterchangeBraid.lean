module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Braid.Thms

/-! # Transport an interchange square by the guarded braid -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InterchangeBraid

open CategoryTheory Silmaril.Isotope.LambdaSSA
open Region.Paper.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem interchange_right_of_left {A B X Y : τ}
    (f : ofType (Φ := Φ) A ⟶ ofType B) (g : ofType X ⟶ ofType Y)
    (h : whiskerRight f (ofType X) ≫ whiskerLeft (ofType B) g =
      whiskerLeft (ofType A) g ≫ whiskerRight f (ofType Y)) :
    whiskerLeft (ofType X) f ≫ whiskerRight g (ofType B) =
      whiskerRight g (ofType A) ≫ whiskerLeft (ofType Y) f := by
  apply (cancel_mono (braidIso (Φ := Φ) Y B).hom).mp
  change (whiskerLeft (ofType X) f ≫ whiskerRight g (ofType B)) ≫ braid Y B =
    (whiskerRight g (ofType A) ≫ whiskerLeft (ofType Y) f) ≫ braid Y B
  erw [Category.assoc, Category.assoc, whiskerRight_braid B g, whiskerLeft_braid Y f,
    ← Category.assoc (whiskerLeft (ofType X) f), ← Category.assoc (whiskerRight g (ofType A)),
    whiskerLeft_braid X f, whiskerRight_braid A g, Category.assoc, Category.assoc, h]
  rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InterchangeBraid
