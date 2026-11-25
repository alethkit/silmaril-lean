module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Associator.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.SharedInput.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.LocalPairing


/-! # Local comparisons for a pairing of two certified arrows -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)

/-- The remaining associator equations are needed only at the three retained pairs. The shuffle
is tested after duplicating the actual shared input. -/
theorem centralCopies_pair_of_local_comparisons {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : CentralCopies f) (hg : CentralCopies g)
    (rightXX : RightAssociatorComparison (Φ := Φ) X X)
    (rightAX : RightAssociatorComparison (Φ := Φ) A X)
    (rightAB : RightAssociatorComparison (Φ := Φ) A B)
    (shuffle :
      pairArrows (diagonalArrow X) (diagonalArrow X) ≫
        middleFour X X X X ≫ tensorSequence (tensorSequence f g) (tensorSequence f g) =
      pairArrows (diagonalArrow X) (diagonalArrow X) ≫
        tensorSequence (tensorSequence f f) (tensorSequence g g) ≫ middleFour A A B B) :
    CentralCopies (pairArrows f g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.LocalPairing.centralCopies_pair_of_local_comparisons hf hg rightXX rightAX rightAB shuffle

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
