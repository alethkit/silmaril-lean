module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Braid.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InterchangeBraid

/-! # The two interchange squares are equivalent by the guarded braid -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory
open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Moving both factors across the braid exchanges their positions in the interchange square. -/
theorem interchange_right_of_left {A B X Y : τ}
    (f : ofType (Φ := Φ) A ⟶ ofType B) (g : ofType X ⟶ ofType Y)
    (h : whiskerRight f (ofType X) ≫ whiskerLeft (ofType B) g =
      whiskerLeft (ofType A) g ≫ whiskerRight f (ofType Y)) :
    whiskerLeft (ofType X) f ≫ whiskerRight g (ofType B) =
      whiskerRight g (ofType A) ≫ whiskerLeft (ofType Y) f :=
  InterchangeBraid.interchange_right_of_left f g h

local notation "Comp" => TypeCategory (τ := τ) Φ

/-- One square against every computation suffices for both squares. -/
theorem whiskerCentral_iff_left {A B : Comp} (f : A ⟶ B) :
    WhiskerCentral f ↔ ∀ {X Y : Comp} (g : X ⟶ Y),
      whiskerRight f X ≫ whiskerLeft B g = whiskerLeft A g ≫ whiskerRight f Y :=
  ⟨fun h {_ _} g => (h g).1, fun h {_ _} g => ⟨h g, interchange_right_of_left (τ := τ) f g (h g)⟩⟩

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- The primitive hypothesis requires one interchange square per marked instruction and computation. -/
theorem primitiveReturnsCentral_iff_left :
    PrimitiveReturnsCentral (τ := τ) (Φ := Φ) pe ↔
      ∀ p : Φ, IsPure pe p → ∀ {X Y : Comp} (g : X ⟶ Y),
        whiskerRight (primitiveReturn (τ := τ) p) X ≫ whiskerLeft (ofType (instrTrg p)) g =
          whiskerLeft (ofType (instrSrc p)) g ≫ whiskerRight (primitiveReturn (τ := τ) p) Y := by
  simp only [PrimitiveReturnsCentral, whiskerCentral_iff_left]

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
