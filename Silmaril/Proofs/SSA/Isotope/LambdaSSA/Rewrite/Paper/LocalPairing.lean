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
    CentralCopies (pairArrows f g) := by
  have fl : WhiskerCentral (whiskerRight f (Obj X)) :=
    whiskerRight_central_of_associator_at X hf.1 associateIso (fun Y => associate_whiskerRight_right X Y f)
      (fun P h => by
        intro Y Z k
        rcases h with e | e
        · subst P
          exact rightXX k
        · subst P
          exact rightAX k)
  have gl : WhiskerCentral (whiskerLeft (Obj A) g) :=
    whiskerLeft_central_of_associator_at A hg.1 associateIso (fun Y => associate_whiskerLeft_right A Y g)
      (fun P h => by
        intro Y Z k
        rcases h with e | e
        · subst P
          exact rightAX k
        · subst P
          exact rightAB k)
  have hd : WhiskerCentral (diagonalArrow (Φ := Φ) X) :=
    whiskerCentral_ofRegion_branchValue (.pair (.var rfl) (.var rfl))
  exact ⟨WhiskerCentral.comp hd (WhiskerCentral.comp fl gl),
    (pairArrows_copy_iff_shared_input_shuffle hf.2 hg).2 shuffle⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.LocalPairing
