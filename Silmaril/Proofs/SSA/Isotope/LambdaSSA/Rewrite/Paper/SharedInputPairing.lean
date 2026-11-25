module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Thms

/-! # Pairing after a common producer and the exact copying square -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SharedInputPairing

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)

local infixr:70 " ×ₜ " => product


set_option backward.isDefEq.respectTransparency false in
theorem pairArrows_comp_common {X Y A B : τ}
    (p : Obj X ⟶ Obj Y) (f : Obj Y ⟶ Obj A) (g : Obj Y ⟶ Obj B)
    (hp : CentralCopies p) :
    pairArrows (p ≫ f) (p ≫ g) = p ≫ pairArrows f g := by
  calc
    _ = pairArrows p p ≫ (whiskerRight f (Obj Y) ≫ whiskerLeft (Obj A) g) := by
      simp only [pairArrows, whiskerRight_comp, whiskerLeft_comp, Category.assoc]
      rw [← Category.assoc (whiskerRight f (Obj X)), ← (hp.1 f).2, Category.assoc]
    _ = _ := by
      have h : pairArrows p p = p ≫ diagonalArrow Y := hp.2
      rw [h, Category.assoc]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem centralCopies_pair_comp_common {X Y A B : τ}
    {p : Obj X ⟶ Obj Y} {f : Obj Y ⟶ Obj A} {g : Obj Y ⟶ Obj B}
    (hp : CentralCopies p) (hpair : CentralCopies (pairArrows f g)) :
    CentralCopies (pairArrows (p ≫ f) (p ≫ g)) := by
  rw [pairArrows_comp_common p f g hp]
  exact ⟨WhiskerCentral.comp hp.1 hpair.1, pairArrows_copy_comp p _ hp.1 hp.2 hpair.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem pairArrows_copy_iff_shared_input_shuffle {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : PreservesDiagonal f) (hg : CentralCopies g) :
    PreservesDiagonal (pairArrows f g) ↔
      pairArrows (diagonalArrow X) (diagonalArrow X) ≫
        middleFour X X X X ≫ tensorSequence (tensorSequence f g) (tensorSequence f g) =
      pairArrows (diagonalArrow X) (diagonalArrow X) ≫
        tensorSequence (tensorSequence f f) (tensorSequence g g) ≫ middleFour A A B B := by
  let d := diagonalArrow (Φ := Φ) X
  have hc : CentralCopies d :=
    ⟨whiskerCentral_ofRegion_branchValue (.pair (.var rfl) (.var rfl)),
      pairArrows_copy_branchValue (.pair (.var rfl) (.var rfl))⟩
  have hc' : pairArrows d d ≫ middleFour X X X X = pairArrows d d := by
    calc
      _ = d ≫ diagonalArrow (X ×ₜ X) := by
        change (d ≫ tensorSequence d d) ≫ middleFour X X X X = _
        rw [Category.assoc, diagonal_tensorSequence]
      _ = _ := hc.2.symm
  have hl : pairArrows (pairArrows f g) (pairArrows f g) =
      pairArrows d d ≫ middleFour X X X X ≫ tensorSequence (tensorSequence f g) (tensorSequence f g) := by
    change pairArrows (d ≫ tensorSequence f g) (d ≫ tensorSequence f g) = _
    rw [pairArrows_comp_common _ _ _ hc, ← Category.assoc, hc', hc.2]
    exact (Category.assoc _ _ _).symm
  have hr : pairArrows f g ≫ diagonalArrow (A ×ₜ B) =
      pairArrows d d ≫ tensorSequence (tensorSequence f f) (tensorSequence g g) ≫ middleFour A A B B := by
    have df : pairArrows f f = f ≫ diagonalArrow A := hf
    have dg : pairArrows g g = g ≫ diagonalArrow B := hg.2
    have hleft : tensorSequence (d ≫ tensorSequence f f) (d ≫ tensorSequence g g) =
        tensorSequence d d ≫ tensorSequence (tensorSequence f f) (tensorSequence g g) :=
      tensorSequence_comp_of_interchange _ _ _ _ ((hc.1 (tensorSequence f f)).2)
    have hright : tensorSequence (f ≫ diagonalArrow A) (g ≫ diagonalArrow B) =
        tensorSequence f g ≫ tensorSequence (diagonalArrow A) (diagonalArrow B) :=
      tensorSequence_comp_of_interchange _ _ _ _ ((hg.1 (diagonalArrow A)).2)
    calc
      _ = d ≫ tensorSequence (f ≫ diagonalArrow A) (g ≫ diagonalArrow B) ≫ middleFour A A B B := by
        rw [hright, Category.assoc, diagonal_tensorSequence]
        change (d ≫ tensorSequence f g) ≫ diagonalArrow (A ×ₜ B) = _
        rw [Category.assoc]
      _ = _ := by
        rw [← df, ← dg]
        change d ≫ tensorSequence (d ≫ tensorSequence f f) (d ≫ tensorSequence g g) ≫
          middleFour A A B B = (d ≫ tensorSequence d d) ≫
            tensorSequence (tensorSequence f f) (tensorSequence g g) ≫ middleFour A A B B
        rw [hleft]
        simp only [Category.assoc]
  change (pairArrows (pairArrows f g) (pairArrows f g) = pairArrows f g ≫ diagonalArrow (A ×ₜ B)) ↔ _
  rw [hl, hr]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SharedInputPairing
