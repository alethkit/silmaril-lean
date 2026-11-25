module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SharedInputPairing

/-! # Copying with a shared input -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)

local infixr:70 " ×ₜ " => product

/-- A central copying producer runs once before the two postcompositions. -/
theorem pairArrows_comp_common {X Y A B : τ}
    (p : Obj X ⟶ Obj Y) (f : Obj Y ⟶ Obj A) (g : Obj Y ⟶ Obj B)
    (hp : CentralCopies p) :
    pairArrows (p ≫ f) (p ≫ g) = p ≫ pairArrows f g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SharedInputPairing.pairArrows_comp_common p f g hp

/-- A certified common producer preserves a certified pairing of its postcompositions. -/
theorem centralCopies_pair_comp_common {X Y A B : τ}
    {p : Obj X ⟶ Obj Y} {f : Obj Y ⟶ Obj A} {g : Obj Y ⟶ Obj B}
    (hp : CentralCopies p) (hpair : CentralCopies (pairArrows f g)) :
    CentralCopies (pairArrows (p ≫ f) (p ≫ g)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SharedInputPairing.centralCopies_pair_comp_common hp hpair

/-- Copying the pairing is exactly the shuffle square after duplicating the shared input. -/
theorem pairArrows_copy_iff_shared_input_shuffle {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : PreservesDiagonal f) (hg : CentralCopies g) :
    PreservesDiagonal (pairArrows f g) ↔
      pairArrows (diagonalArrow X) (diagonalArrow X) ≫
        middleFour X X X X ≫ tensorSequence (tensorSequence f g) (tensorSequence f g) =
      pairArrows (diagonalArrow X) (diagonalArrow X) ≫
        tensorSequence (tensorSequence f f) (tensorSequence g g) ≫ middleFour A A B B :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SharedInputPairing.pairArrows_copy_iff_shared_input_shuffle hf hg

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
