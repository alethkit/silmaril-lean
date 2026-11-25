module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductShuffle

/-! # Structural and local coherence laws for pairing -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)
local infixr:70 " ×ₜ " => product

/-- Copying a product is the two factor diagonals followed by the guarded shuffle. -/
theorem diagonal_tensorSequence (A B : τ) :
    tensorSequence (diagonalArrow (Φ := Φ) A) (diagonalArrow B) ≫ middleFour A A B B =
      diagonalArrow (A ×ₜ B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductShuffle.diagonal_tensorSequence A B

/-- Naturality of the shuffle transports the diagonal laws of the two factors. -/
theorem tensorSequence_copies_of_shuffle {X Y A B : τ} {f : Obj X ⟶ Obj A} {g : Obj Y ⟶ Obj B}
    (cg : WhiskerCentral g) (cfCopy : PreservesDiagonal f) (cgCopy : PreservesDiagonal g)
    (shuffle : middleFour X X Y Y ≫ tensorSequence (tensorSequence f g) (tensorSequence f g) =
      tensorSequence (tensorSequence f f) (tensorSequence g g) ≫ middleFour A A B B) :
    PreservesDiagonal (tensorSequence f g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductShuffle.tensorSequence_copies_of_shuffle cg cfCopy cgCopy shuffle

/-- The two local interchange certificates and the middle-four square certify the canonical pairing. -/
theorem pairArrows_centralCopies_of_shuffle {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : CentralCopies f) (hg : CentralCopies g)
    (left : WhiskerCentral (whiskerRight f (Obj X)))
    (right : WhiskerCentral (whiskerLeft (Obj A) g))
    (shuffle : middleFour X X X X ≫ tensorSequence (tensorSequence f g) (tensorSequence f g) =
      tensorSequence (tensorSequence f f) (tensorSequence g g) ≫ middleFour A A B B) :
    CentralCopies (pairArrows f g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductShuffle.pairArrows_centralCopies_of_shuffle hf hg left right shuffle

/-- Middle- and right-factor associator naturality transport centrality through left whiskering. -/
theorem whiskerLeft_central_of_associator {A B : τ} {f : Obj A ⟶ Obj B} (X : τ)
    (hf : WhiskerCentral f)
    (assoc : ∀ P Q R : τ, Obj ((P ×ₜ Q) ×ₜ R) ≅ Obj (P ×ₜ Q ×ₜ R))
    (middle : ∀ Y : τ, whiskerRight (whiskerLeft (Obj X) f) (Obj Y) ≫ (assoc X B Y).hom =
      (assoc X A Y).hom ≫ whiskerLeft (Obj X) (whiskerRight f (Obj Y)))
    (right : ∀ (P : τ) {Y Z : τ} (g : Obj Y ⟶ Obj Z),
      whiskerLeft (Obj (X ×ₜ P)) g ≫ (assoc X P Z).hom =
        (assoc X P Y).hom ≫ whiskerLeft (Obj X) (whiskerLeft (Obj P) g)) :
    WhiskerCentral (whiskerLeft (Obj X) f) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductShuffle.whiskerLeft_central_of_associator X hf assoc middle right

/-- Left- and right-factor associator naturality transport centrality through right whiskering. -/
theorem whiskerRight_central_of_associator {A B : τ} {f : Obj A ⟶ Obj B} (X : τ)
    (hf : WhiskerCentral f)
    (assoc : ∀ P Q R : τ, Obj ((P ×ₜ Q) ×ₜ R) ≅ Obj (P ×ₜ Q ×ₜ R))
    (left : ∀ Y : τ, whiskerRight (whiskerRight f (Obj X)) (Obj Y) ≫ (assoc B X Y).hom =
      (assoc A X Y).hom ≫ whiskerRight f (Obj (X ×ₜ Y)))
    (right : ∀ (P : τ) {Y Z : τ} (g : Obj Y ⟶ Obj Z),
      whiskerLeft (Obj (P ×ₜ X)) g ≫ (assoc P X Z).hom =
        (assoc P X Y).hom ≫ whiskerLeft (Obj P) (whiskerLeft (Obj X) g)) :
    WhiskerCentral (whiskerRight f (Obj X)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductShuffle.whiskerRight_central_of_associator X hf assoc left right

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
