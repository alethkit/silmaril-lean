module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Associator.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.SharedInput.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Thms

/-! # The associator and shuffle comparisons for the canonical pairing -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.LocalPairing

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)

set_option backward.isDefEq.respectTransparency false in
theorem whiskerCentral_pair {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : WhiskerCentral f) (hg : WhiskerCentral g) : WhiskerCentral (pairArrows f g) := by
  have fl : WhiskerCentral (whiskerRight f (Obj X)) :=
    whiskerRight_central_of_associator X hf associateIso
      (fun Y => associate_whiskerRight_right X Y f) (fun P {_ _} k => associate_whiskerLeft_left P X k)
  have gl : WhiskerCentral (whiskerLeft (Obj A) g) :=
    whiskerLeft_central_of_associator A hg associateIso
      (fun Y => associate_whiskerLeft_right A Y g) (fun P {_ _} k => associate_whiskerLeft_left A P k)
  have hd : WhiskerCentral (diagonalArrow (Φ := Φ) X) :=
    whiskerCentral_ofRegion_branchValue (.pair (.var rfl) (.var rfl))
  unfold pairArrows
  exact fun {_ _} k => WhiskerCentral.comp hd (WhiskerCentral.comp fl gl) k

theorem centralCopies_pair_of_shared_input_shuffle {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : CentralCopies f) (hg : CentralCopies g)
    (shuffle :
      pairArrows (diagonalArrow X) (diagonalArrow X) ≫
        middleFour X X X X ≫ tensorSequence (tensorSequence f g) (tensorSequence f g) =
      pairArrows (diagonalArrow X) (diagonalArrow X) ≫
        tensorSequence (tensorSequence f f) (tensorSequence g g) ≫ middleFour A A B B) :
    CentralCopies (pairArrows f g) :=
  ⟨whiskerCentral_pair hf.1 hg.1, (pairArrows_copy_iff_shared_input_shuffle hf.2 hg).2 shuffle⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.LocalPairing
