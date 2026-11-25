module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Associator.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.SharedInput.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.LocalPairing


/-! # Pairing of central arrows and the remaining copying equation -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)

/-- Pairing preserves centrality in the default singleton quotient. -/
theorem whiskerCentral_pair {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : WhiskerCentral f) (hg : WhiskerCentral g) : WhiskerCentral (pairArrows f g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.LocalPairing.whiskerCentral_pair hf hg

/-- Copying the pair only needs the shuffle tested on the duplicated shared input. -/
theorem centralCopies_pair_of_shared_input_shuffle {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : CentralCopies f) (hg : CentralCopies g)
    (shuffle :
      pairArrows (diagonalArrow X) (diagonalArrow X) ≫
        middleFour X X X X ≫ tensorSequence (tensorSequence f g) (tensorSequence f g) =
      pairArrows (diagonalArrow X) (diagonalArrow X) ≫
        tensorSequence (tensorSequence f f) (tensorSequence g g) ≫ middleFour A A B B) :
    CentralCopies (pairArrows f g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.LocalPairing.centralCopies_pair_of_shared_input_shuffle hf hg shuffle

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
