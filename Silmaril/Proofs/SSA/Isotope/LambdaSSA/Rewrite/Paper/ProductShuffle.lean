module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Interchange.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs

/-! # Structural diagonal and local coherence for pairing -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductShuffle

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper (Eqv)
open Paper.TypeCategory
open CfgEta.TypeCategory (seqValueBranches whiskerLeftRegion_typed whiskerRightRegion_typed)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)
local infixr:70 " ×ₜ " => product

set_option backward.isDefEq.respectTransparency false in
private theorem tensorSequence_comp_of_interchange {A B C D E F : τ}
    (f : Obj A ⟶ Obj C) (g : Obj B ⟶ Obj D) (h : Obj C ⟶ Obj E) (k : Obj D ⟶ Obj F)
    (swap : whiskerLeft (Obj C) g ≫ whiskerRight h (Obj D) =
      whiskerRight h (Obj B) ≫ whiskerLeft (Obj E) g) :
    tensorSequence (f ≫ h) (g ≫ k) = tensorSequence f g ≫ tensorSequence h k := by
  simp only [tensorSequence, whiskerRight_comp, whiskerLeft_comp, Category.assoc]
  rw [← Category.assoc (whiskerLeft (Obj C) g), swap, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem diagonal_tensorSequence (A B : τ) :
    tensorSequence (diagonalArrow (Φ := Φ) A) (diagonalArrow B) ≫ middleFour A A B B =
      diagonalArrow (A ×ₜ B) := by
  unfold tensorSequence diagonalArrow middleFour
  rw [whiskerRight_ofRegion, whiskerLeft_ofRegion]
  unfold tensorObj
  let p := whiskerRightRegion_typed B (Paper.RetainedLet.diagonal_typed (Φ := Φ) A)
  let q := whiskerLeftRegion_typed (A ×ₜ A) (Paper.RetainedLet.diagonal_typed (Φ := Φ) B)
  let m := middleFour_typed (Φ := Φ) A A B B
  rw [ofRegion_comp _ _ (seqValueBranches p q), ofRegion_comp _ _ (seqValueBranches (seqValueBranches p q) m)]
  apply (ofRegion_eq_iff _ _).mpr
  apply (Paper.product_variable_eta_iff (i := 0) (A := A) (B := B)
    (rfl : At [A ×ₜ B] 0 (A ×ₜ B)) (seqValueBranches (seqValueBranches p q) m).hasType
    (Paper.RetainedLet.diagonal_typed (Φ := Φ) (A ×ₜ B)).hasType).mp
  let Γ : VCtx τ := [B, A, A ×ₜ B]
  let a : Tm.BranchValue Γ (.var 1 : Tm Φ) A := .var rfl
  let b : Tm.BranchValue Γ (.var 0 : Tm Φ) B := .var rfl
  change Eqv Γ (.let₂ (.pair (.var 1) (.var 0))
    (.let₂ (.pair (.pair (.var 1) (.var 1)) (.var 0))
      (.let₂ (.pair (.var 1) (.pair (.var 0) (.var 0)))
        (.let₂ (.var 1) (.let₂ (.var 2)
          (.br 0 (.pair (.pair (.var 3) (.var 1)) (.pair (.var 2) (.var 0)))))))))
    (.br 0 (.pair (.pair (.var 1) (.var 0)) (.pair (.var 1) (.var 0)))) [(A ×ₜ B) ×ₜ A ×ₜ B]
  refine Eqv.trans (.productBeta (.let₂Beta a b ?_)) ?_
  · exact .let₂ (A := A ×ₜ A) (B := B) (.pair (.pair (.var rfl) (.var rfl)) (.var rfl))
      (.let₂ (A := A ×ₜ A) (B := B ×ₜ B) (.pair (.var rfl) (.pair (.var rfl) (.var rfl)))
        (.let₂ (A := A) (B := A) (.var rfl) (.let₂ (A := B) (B := B) (.var rfl)
          (.br rfl (.pair (.pair (.var rfl) (.var rfl)) (.pair (.var rfl) (.var rfl)))))))
  refine Eqv.trans (.productBeta (.let₂Beta (.pair a a) b ?_)) ?_
  · exact .let₂ (A := A ×ₜ A) (B := B ×ₜ B) (.pair (.var rfl) (.pair (.var rfl) (.var rfl)))
      (.let₂ (A := A) (B := A) (.var rfl) (.let₂ (A := B) (B := B) (.var rfl)
        (.br rfl (.pair (.pair (.var rfl) (.var rfl)) (.pair (.var rfl) (.var rfl))))))
  refine Eqv.trans (.productBeta (.let₂Beta (.pair a a) (.pair b b) ?_)) ?_
  · exact .let₂ (A := A) (B := A) (.var rfl) (.let₂ (A := B) (B := B) (.var rfl)
      (.br rfl (.pair (.pair (.var rfl) (.var rfl)) (.pair (.var rfl) (.var rfl)))))
  refine Eqv.trans (.productBeta (.let₂Beta a a ?_)) ?_
  · exact .let₂ (A := B) (B := B) (.pair (.var (i := 2) rfl) (.var (i := 2) rfl))
      (.br rfl (.pair (.pair (.var rfl) (.var rfl)) (.pair (.var rfl) (.var rfl))))
  apply Eqv.productBeta
  apply ProductBeta.Step.let₂Beta b b
  exact .br rfl (.pair (.pair (.var (i := 3) rfl) (.var (i := 1) rfl))
    (.pair (.var (i := 3) rfl) (.var (i := 0) rfl)))


private theorem diagonal_central (A : τ) :
    WhiskerCentral (diagonalArrow (Φ := Φ) A) :=
  whiskerCentral_ofRegion_branchValue (.pair (.var rfl) (.var rfl))

private theorem diagonal_copies (A : τ) :
    PreservesDiagonal (diagonalArrow (Φ := Φ) A) :=
  pairArrows_copy_branchValue (.pair (.var rfl) (.var rfl))

set_option backward.isDefEq.respectTransparency false in
theorem tensorSequence_copies_of_shuffle {X Y A B : τ} {f : Obj X ⟶ Obj A} {g : Obj Y ⟶ Obj B}
    (cg : WhiskerCentral g) (cfCopy : PreservesDiagonal f) (cgCopy : PreservesDiagonal g)
    (shuffle : middleFour X X Y Y ≫ tensorSequence (tensorSequence f g) (tensorSequence f g) =
      tensorSequence (tensorSequence f f) (tensorSequence g g) ≫ middleFour A A B B) :
    PreservesDiagonal (tensorSequence f g) := by
  change diagonalArrow (X ×ₜ Y) ≫ tensorSequence (tensorSequence f g) (tensorSequence f g) =
    tensorSequence f g ≫ diagonalArrow (A ×ₜ B)
  have df : diagonalArrow X ≫ tensorSequence f f = f ≫ diagonalArrow A := cfCopy
  have dg : diagonalArrow Y ≫ tensorSequence g g = g ≫ diagonalArrow B := cgCopy
  calc
    _ = (tensorSequence (diagonalArrow X) (diagonalArrow Y) ≫
        tensorSequence (tensorSequence f f) (tensorSequence g g)) ≫ middleFour A A B B := by
      rw [← diagonal_tensorSequence X Y, Category.assoc, shuffle, Category.assoc]
      simp only [tensorSequence, Category.assoc]
    _ = tensorSequence (diagonalArrow X ≫ tensorSequence f f)
        (diagonalArrow Y ≫ tensorSequence g g) ≫ middleFour A A B B := by
      rw [tensorSequence_comp_of_interchange _ _ _ _ ((diagonal_central Y) (tensorSequence f f)).2]
    _ = (tensorSequence f g ≫ tensorSequence (diagonalArrow A) (diagonalArrow B)) ≫
        middleFour A A B B := by
      rw [df, dg, tensorSequence_comp_of_interchange _ _ _ _ (cg (diagonalArrow A)).2]
    _ = _ := by rw [Category.assoc, diagonal_tensorSequence A B]

set_option backward.isDefEq.respectTransparency false in
theorem pairArrows_centralCopies_of_shuffle {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : CentralCopies f) (hg : CentralCopies g)
    (left : WhiskerCentral (whiskerRight f (Obj X)))
    (right : WhiskerCentral (whiskerLeft (Obj A) g))
    (shuffle : middleFour X X X X ≫ tensorSequence (tensorSequence f g) (tensorSequence f g) =
      tensorSequence (tensorSequence f f) (tensorSequence g g) ≫ middleFour A A B B) :
    CentralCopies (pairArrows f g) := by
  change CentralCopies (diagonalArrow X ≫ tensorSequence f g)
  have d : WhiskerCentral (diagonalArrow (Φ := Φ) X) := diagonal_central X
  exact ⟨WhiskerCentral.comp d (WhiskerCentral.comp left right), pairArrows_copy_comp _ _ d (diagonal_copies X)
    (tensorSequence_copies_of_shuffle hg.1 hf.2 hg.2 shuffle)⟩

set_option backward.isDefEq.respectTransparency false in
theorem whiskerLeft_central_of_associator {A B : τ} {f : Obj A ⟶ Obj B} (X : τ)
    (hf : WhiskerCentral f)
    (assoc : ∀ P Q R : τ, Obj ((P ×ₜ Q) ×ₜ R) ≅ Obj (P ×ₜ Q ×ₜ R))
    (middle : ∀ Y : τ, whiskerRight (whiskerLeft (Obj X) f) (Obj Y) ≫ (assoc X B Y).hom =
      (assoc X A Y).hom ≫ whiskerLeft (Obj X) (whiskerRight f (Obj Y)))
    (right : ∀ (P : τ) {Y Z : τ} (g : Obj Y ⟶ Obj Z),
      whiskerLeft (Obj (X ×ₜ P)) g ≫ (assoc X P Z).hom =
        (assoc X P Y).hom ≫ whiskerLeft (Obj X) (whiskerLeft (Obj P) g)) :
    WhiskerCentral (whiskerLeft (Obj X) f) := by
  apply (whiskerCentral_iff_left _).2
  intro Y Z g
  apply (cancel_mono (assoc X B Z).hom).mp
  change (whiskerRight (whiskerLeft (Obj X) f) (Obj Y) ≫ whiskerLeft (Obj (X ×ₜ B)) g) ≫
      (assoc X B Z).hom =
    (whiskerLeft (Obj (X ×ₜ A)) g ≫ whiskerRight (whiskerLeft (Obj X) f) (Obj Z)) ≫
      (assoc X B Z).hom
  calc
    _ = (assoc X A Y).hom ≫ whiskerLeft (Obj X)
        (whiskerRight f (Obj Y) ≫ whiskerLeft (Obj B) g) := by
      rw [Category.assoc, right B g, ← Category.assoc, middle Y, Category.assoc, ← whiskerLeft_comp]
    _ = (assoc X A Y).hom ≫ whiskerLeft (Obj X)
        (whiskerLeft (Obj A) g ≫ whiskerRight f (Obj Z)) := by rw [(hf g).1]
    _ = _ := by
      rw [Category.assoc, middle Z, ← Category.assoc, right A g, Category.assoc, ← whiskerLeft_comp]

set_option backward.isDefEq.respectTransparency false in
theorem whiskerRight_central_of_associator {A B : τ} {f : Obj A ⟶ Obj B} (X : τ)
    (hf : WhiskerCentral f)
    (assoc : ∀ P Q R : τ, Obj ((P ×ₜ Q) ×ₜ R) ≅ Obj (P ×ₜ Q ×ₜ R))
    (left : ∀ Y : τ, whiskerRight (whiskerRight f (Obj X)) (Obj Y) ≫ (assoc B X Y).hom =
      (assoc A X Y).hom ≫ whiskerRight f (Obj (X ×ₜ Y)))
    (right : ∀ (P : τ) {Y Z : τ} (g : Obj Y ⟶ Obj Z),
      whiskerLeft (Obj (P ×ₜ X)) g ≫ (assoc P X Z).hom =
        (assoc P X Y).hom ≫ whiskerLeft (Obj P) (whiskerLeft (Obj X) g)) :
    WhiskerCentral (whiskerRight f (Obj X)) := by
  apply (whiskerCentral_iff_left _).2
  intro Y Z g
  apply (cancel_mono (assoc B X Z).hom).mp
  change (whiskerRight (whiskerRight f (Obj X)) (Obj Y) ≫ whiskerLeft (Obj (B ×ₜ X)) g) ≫
      (assoc B X Z).hom =
    (whiskerLeft (Obj (A ×ₜ X)) g ≫ whiskerRight (whiskerRight f (Obj X)) (Obj Z)) ≫
      (assoc B X Z).hom
  calc
    _ = (assoc A X Y).hom ≫ (whiskerRight f (Obj (X ×ₜ Y)) ≫
        whiskerLeft (Obj B) (whiskerLeft (Obj X) g)) := by
      rw [Category.assoc, right B g, ← Category.assoc, left Y, Category.assoc]
    _ = (assoc A X Y).hom ≫ (whiskerLeft (Obj A) (whiskerLeft (Obj X) g) ≫
        whiskerRight f (Obj (X ×ₜ Z))) :=
      congrArg ((assoc A X Y).hom ≫ ·) ((hf (whiskerLeft (Obj X) g)).1)
    _ = _ := by
      symm
      rw [Category.assoc, left Z, ← Category.assoc, right A g, Category.assoc]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductShuffle
