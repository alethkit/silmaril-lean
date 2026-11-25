module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.LocalPairing.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Braid.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs

/-! # The guarded middle-four permutation and its computation comparison -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MiddleFourInterchange

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory Paper.TypeCategory


universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
local notation "Obj" => ofType (τ := τ) (Φ := Φ)
local infixr:70 " ×ₜ " => product
local infixr:70 " ⊗ₛ " => tensorSequence

set_option allowUnsafeReducibility true in
attribute [local reducible] tensorObj

set_option backward.isDefEq.respectTransparency false in
private theorem tensorSequence_associate
    {A B C X Y Z : τ} (f : Obj X ⟶ Obj A) (g : Obj Y ⟶ Obj B) (h : Obj Z ⟶ Obj C) :
    ((f ⊗ₛ g) ⊗ₛ h) ≫ associate A B C = associate X Y Z ≫ (f ⊗ₛ (g ⊗ₛ h)) := by
  simp only [tensorSequence, whiskerRight_comp, whiskerLeft_comp, Category.assoc]
  rw [associate_whiskerLeft_left, ← Category.assoc (whiskerRight (whiskerLeft (Obj A) g) (Obj Z)),
    associate_whiskerLeft_right, Category.assoc, ← Category.assoc (whiskerRight (whiskerRight f (Obj Y)) (Obj Z)),
    associate_whiskerRight_right, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem tensorSequence_unassociate
    {A B C X Y Z : τ} (f : Obj X ⟶ Obj A) (g : Obj Y ⟶ Obj B) (h : Obj Z ⟶ Obj C) :
    (f ⊗ₛ (g ⊗ₛ h)) ≫ unassociate A B C = unassociate X Y Z ≫ ((f ⊗ₛ g) ⊗ₛ h) := by
  have e := congrArg (fun k => unassociate X Y Z ≫ k) (tensorSequence_associate f g h)
  rw [← Category.assoc (unassociate X Y Z) (associate X Y Z),
    unassociate_associate, Category.id_comp] at e
  apply (cancel_mono (associateIso A B C).hom).mp
  simpa only [associateIso, Category.assoc, unassociate_associate, Category.comp_id] using e.symm

set_option backward.isDefEq.respectTransparency false in
theorem tensorSequence_braid_of_central
    {A B X Y : τ} (f : Obj X ⟶ Obj A) {g : Obj Y ⟶ Obj B} (hg : WhiskerCentral g) :
    (f ⊗ₛ g) ≫ braid A B = braid X Y ≫ (g ⊗ₛ f) := by
  simp only [tensorSequence, Category.assoc]
  rw [whiskerLeft_braid, ← Category.assoc (whiskerRight f (Obj Y)), whiskerRight_braid, Category.assoc]
  exact congrArg (fun k => braid X Y ≫ k) (hg f).1.symm

private abbrev swapLeading (A B C : τ) : Obj (A ×ₜ B ×ₜ C) ⟶ Obj (B ×ₜ A ×ₜ C) :=
  unassociate A B C ≫ whiskerRight (braid A B) (Obj C) ≫ associate B A C

private theorem tensorSequence_swapLeading
    {A B C X Y Z : τ} (f : Obj X ⟶ Obj A) {g : Obj Y ⟶ Obj B} (h : Obj Z ⟶ Obj C)
    (hg : WhiskerCentral g) (ch : WhiskerCentral h) :
    (f ⊗ₛ (g ⊗ₛ h)) ≫ swapLeading A B C = swapLeading X Y Z ≫ (g ⊗ₛ (f ⊗ₛ h)) := by
  have hs :
      ((f ⊗ₛ g) ⊗ₛ h) ≫ whiskerRight (braid A B) (Obj C) =
        whiskerRight (braid X Y) (Obj Z) ≫ ((g ⊗ₛ f) ⊗ₛ h) := by
    have h₁ : (((f ⊗ₛ g) ≫ braid A B) ⊗ₛ h) =
        ((f ⊗ₛ g) ⊗ₛ h) ≫ whiskerRight (braid A B) (Obj C) := by
      simpa only [tensorSequence, whiskerLeft_id, Category.assoc, Category.id_comp, Category.comp_id] using
        tensorSequence_comp_of_interchange (f ⊗ₛ g) h (braid A B) (𝟙 (Obj C)) ((ch (braid A B)).2)
    have h₂ : ((braid X Y ≫ (g ⊗ₛ f)) ⊗ₛ h) =
        whiskerRight (braid X Y) (Obj Z) ≫ ((g ⊗ₛ f) ⊗ₛ h) := by
      simpa only [tensorSequence, whiskerLeft_id, Category.assoc, Category.id_comp, Category.comp_id] using
        tensorSequence_comp_of_interchange (braid X Y) (𝟙 (Obj Z)) (g ⊗ₛ f) h (by
          simp [whiskerLeft_id])
    exact h₁.symm.trans ((congrArg (fun k => k ⊗ₛ h) (tensorSequence_braid_of_central f hg)).trans h₂)
  calc
    _ = ((f ⊗ₛ (g ⊗ₛ h)) ≫ unassociate A B C) ≫ whiskerRight (braid A B) (Obj C) ≫ associate B A C := by
      simp only [swapLeading, Category.assoc]
    _ = unassociate X Y Z ≫
        (((f ⊗ₛ g) ⊗ₛ h) ≫ whiskerRight (braid A B) (Obj C)) ≫ associate B A C := by
      rw [tensorSequence_unassociate]
      simp only [Category.assoc]
    _ = unassociate X Y Z ≫ whiskerRight (braid X Y) (Obj Z) ≫
        (((g ⊗ₛ f) ⊗ₛ h) ≫ associate B A C) := by
      rw [hs]
      simp only [Category.assoc]
    _ = _ := by
      erw [tensorSequence_associate]
      simp only [swapLeading, Category.assoc]

private abbrev factored (A C B D : τ) : Obj ((A ×ₜ C) ×ₜ (B ×ₜ D)) ⟶ Obj ((A ×ₜ B) ×ₜ (C ×ₜ D)) :=
  associate A C (B ×ₜ D) ≫ whiskerLeft (Obj A) (swapLeading C B D) ≫ unassociate A B (C ×ₜ D)

private theorem factored_natural
    {A B C D X Y Z W : τ} {f : Obj X ⟶ Obj A} (g : Obj Y ⟶ Obj B)
    {h : Obj Z ⟶ Obj C} (i : Obj W ⟶ Obj D)
    (hf : WhiskerCentral f) (hh : WhiskerCentral h) (hi : WhiskerCentral i) :
    ((f ⊗ₛ g) ⊗ₛ (h ⊗ₛ i)) ≫ factored A B C D =
      factored X Y Z W ≫ ((f ⊗ₛ h) ⊗ₛ (g ⊗ₛ i)) := by
  have hs :
      (f ⊗ₛ (g ⊗ₛ (h ⊗ₛ i))) ≫ whiskerLeft (Obj A) (swapLeading B C D) =
        whiskerLeft (Obj X) (swapLeading Y Z W) ≫ (f ⊗ₛ (h ⊗ₛ (g ⊗ₛ i))) := by
    have h₁ : (f ⊗ₛ ((g ⊗ₛ (h ⊗ₛ i)) ≫ swapLeading B C D)) =
        (f ⊗ₛ (g ⊗ₛ (h ⊗ₛ i))) ≫ whiskerLeft (Obj A) (swapLeading B C D) := by
      simpa only [tensorSequence, whiskerRight_id, Category.assoc, Category.id_comp, Category.comp_id] using
        tensorSequence_comp_of_interchange f (g ⊗ₛ (h ⊗ₛ i)) (𝟙 (Obj A)) (swapLeading B C D) (by
          simp [whiskerRight_id])
    have h₂ : (f ⊗ₛ (swapLeading Y Z W ≫ (h ⊗ₛ (g ⊗ₛ i)))) =
        whiskerLeft (Obj X) (swapLeading Y Z W) ≫ (f ⊗ₛ (h ⊗ₛ (g ⊗ₛ i))) := by
      simpa only [tensorSequence, whiskerRight_id, Category.assoc, Category.id_comp, Category.comp_id] using
        tensorSequence_comp_of_interchange (𝟙 (Obj X)) (swapLeading Y Z W) f (h ⊗ₛ (g ⊗ₛ i))
          ((hf (swapLeading Y Z W)).1.symm)
    exact h₁.symm.trans ((congrArg (fun k => f ⊗ₛ k) (tensorSequence_swapLeading g i hh hi)).trans h₂)
  calc
    _ = (((f ⊗ₛ g) ⊗ₛ (h ⊗ₛ i)) ≫ associate A B (C ×ₜ D)) ≫
        whiskerLeft (Obj A) (swapLeading B C D) ≫ unassociate A C (B ×ₜ D) := by
      simp only [factored, Category.assoc]
    _ = associate X Y (Z ×ₜ W) ≫ ((f ⊗ₛ (g ⊗ₛ (h ⊗ₛ i))) ≫
        whiskerLeft (Obj A) (swapLeading B C D)) ≫ unassociate A C (B ×ₜ D) := by
      erw [tensorSequence_associate]
      simp only [Category.assoc]
    _ = associate X Y (Z ×ₜ W) ≫ whiskerLeft (Obj X) (swapLeading Y Z W) ≫
        ((f ⊗ₛ (h ⊗ₛ (g ⊗ₛ i))) ≫ unassociate A C (B ×ₜ D)) := by
      rw [hs]
      simp only [Category.assoc]
    _ = _ := by
      erw [tensorSequence_unassociate]
      simp only [factored, Category.assoc]

open Paper (Eqv)
open CfgEta.TypeCategory (seqValueBranches whiskerLeftRegion whiskerRightRegion
  whiskerLeftRegion_typed whiskerRightRegion_typed whiskerLeftBody whiskerRightBody)

private abbrev seq (r s : Region Φ) := compLSubst (fun _ => r) (fun _ => s) 0
private abbrev factoredRegion {Φ : Type v} : Region Φ :=
  seq (seq associateRegion (whiskerLeftRegion (seq (seq unassociateRegion
    (whiskerRightRegion braidRegion)) associateRegion))) unassociateRegion

private abbrev factoredTail {Φ : Type v} : Region Φ :=
  (.let₂ (.var 1)
    (.let₂ (.pair (.var 1) (.pair (.var 0) (.var 2)))
      (.let₂ (.var 0) (.let₂ (.var 0)
        (.let₂ (.pair (.pair (.var 3) (.var 1)) (.var 0)) (.let₂ (.var 1)
          (.let₂ (.pair (.pair (.var 0) (.var 1)) (.var 2)) (.let₂ (.var 1)
            (.let₂ (.pair (.var 13) (.pair (.var 1) (.pair (.var 0) (.var 2))))
              (.let₂ (.var 0) (.br 0 (.pair (.pair (.var 3) (.var 1)) (.var 0)))))))))))))

private abbrev expandedFactoredRegion {Φ : Type v} : Region Φ :=
  .let₂ (.var 0) factoredTail

private theorem factoredRegion_expand {Φ : Type v} :
    (factoredRegion : Region Φ) = expandedFactoredRegion := by
  simp only [factoredRegion, expandedFactoredRegion, factoredTail, seq, compLSubst, whiskerLeftRegion, whiskerRightRegion,
    whiskerLeftBody, whiskerRightBody, braidRegion, associateRegion, unassociateRegion,
    renameVars, lsubst, liftLSubstVars, substVars, Tm.rename, Tm.subst]
  rfl

-- Typing in this fixed representative uses only guarded lets, branches, pairs and variables.
local macro "typeStructural" : tactic =>
  `(tactic| repeat first
      | apply HasType.let₂
      | apply HasType.br
      | apply Tm.HasType.pair
      | apply Tm.HasType.var
      | apply Tm.BranchValue.pair
      | apply Tm.BranchValue.var
      | rfl)

local macro "structuralBeta " T:term "," U:term : tactic =>
  `(tactic|
    (refine Eqv.trans (.productBeta (.let₂Beta (A := $T) (B := $U) ?left ?right ?body)) ?_
     case left => typeStructural
     case right => typeStructural
     case body => typeStructural
     conv => arg 2; reduce))

set_option backward.isDefEq.respectTransparency false in
private theorem normalizeFactored {Γ : VCtx τ} (A C B D : τ) :
    Eqv (Φ := Φ) (D :: B :: C :: A :: Γ)
      (.let₂ (.pair (.pair (.var 3) (.var 2)) (.pair (.var 1) (.var 0))) factoredTail)
      (.let₂ (.pair (.pair (.var 3) (.var 2)) (.pair (.var 1) (.var 0)))
        (.let₂ (.var 1) (.let₂ (.var 2)
          (.br 0 (.pair (.pair (.var 3) (.var 1)) (.pair (.var 2) (.var 0)))))))
      [(A ×ₜ B) ×ₜ (C ×ₜ D)] := by
  apply Eqv.trans (s := .br 0 (.pair (.pair (.var 3) (.var 1)) (.pair (.var 2) (.var 0))))
  · structuralBeta (A ×ₜ C), (B ×ₜ D)
    structuralBeta A, C
    structuralBeta A, (C ×ₜ B ×ₜ D)
    structuralBeta C, (B ×ₜ D)
    structuralBeta B, D
    structuralBeta (C ×ₜ B), D
    structuralBeta C, B
    structuralBeta (B ×ₜ C), D
    structuralBeta B, C
    structuralBeta A, (B ×ₜ C ×ₜ D)
    structuralBeta B, (C ×ₜ D)
    exact .refl (by typeStructural)
  · apply Eqv.symm
    structuralBeta (A ×ₜ C), (B ×ₜ D)
    structuralBeta A, C
    structuralBeta B, D
    exact .refl (by typeStructural)

set_option backward.isDefEq.respectTransparency false in
private theorem factored_eq_middleFour (A C B D : τ) :
    factored (Φ := Φ) A C B D = middleFour A C B D := by
  unfold factored swapLeading middleFour braid
  let un := unassociate_typed (Φ := Φ) C B D
  let swap := whiskerRightRegion_typed D (braidBranches (Φ := Φ) C B)
  let first := associate_typed (Φ := Φ) A C (B ×ₜ D)
  let last := unassociate_typed (Φ := Φ) A B (C ×ₜ D)
  let inner := seqValueBranches (seqValueBranches un swap) (associate_typed B C D)
  rw [whiskerRight_ofRegion, ← Category.assoc (unassociate C B D),
    ofRegion_comp _ _ (seqValueBranches un swap), ofRegion_comp _ _ inner, whiskerLeft_ofRegion]
  unfold tensorObj
  let stage := seqValueBranches first (whiskerLeftRegion_typed A inner)
  let full := seqValueBranches stage last
  rw [← Category.assoc (associate A C (B ×ₜ D)), ofRegion_comp _ _ stage, ofRegion_comp _ _ full]
  apply (ofRegion_eq_iff _ _).2
  change Eqv [(A ×ₜ C) ×ₜ (B ×ₜ D)] factoredRegion middleFourRegion [(A ×ₜ B) ×ₜ (C ×ₜ D)]
  -- Expose the four leaves in both representatives before reducing their constructor guards.
  let Γ : VCtx τ := [(A ×ₜ C) ×ₜ (B ×ₜ D)]
  let ε₀ : At Γ 0 ((A ×ₜ C) ×ₜ (B ×ₜ D)) := rfl
  rw [factoredRegion_expand]
  let left₀ : HasType Γ (expandedFactoredRegion : Region Φ) [(A ×ₜ B) ×ₜ (C ×ₜ D)] :=
    factoredRegion_expand ▸ full.hasType
  let right₀ := (middleFour_typed (Φ := Φ) A C B D).hasType
  let e₀ := Paper.product_variable_eta_iff ε₀ left₀ right₀
  apply e₀.mp
  let left₁ := ((Paper.product_variable_eta_iff ε₀ left₀ left₀).mpr (.refl left₀)).typed.1
  let right₁ := ((Paper.product_variable_eta_iff ε₀ right₀ right₀).mpr (.refl right₀)).typed.1
  let ε₁ : At (B ×ₜ D :: A ×ₜ C :: Γ) 1 (A ×ₜ C) := rfl
  apply (Paper.product_variable_eta_iff ε₁ left₁ right₁).mp
  let left₂ := ((Paper.product_variable_eta_iff ε₁ left₁ left₁).mpr (.refl left₁)).typed.1
  let right₂ := ((Paper.product_variable_eta_iff ε₁ right₁ right₁).mpr (.refl right₁)).typed.1
  let ε₂ : At (C :: A :: B ×ₜ D :: A ×ₜ C :: Γ) 2 (B ×ₜ D) := rfl
  apply (Paper.product_variable_eta_iff ε₂ left₂ right₂).mp
  conv => arg 2; reduce
  conv => arg 3; reduce
  exact normalizeFactored A C B D

theorem middleFour_factorization (A C B D : τ) :
    middleFour (Φ := Φ) A C B D =
      associate A C (B ×ₜ D) ≫ whiskerLeft (Obj A)
        (unassociate C B D ≫ whiskerRight (braid C B) (Obj D) ≫ associate B C D) ≫
        unassociate A B (C ×ₜ D) :=
  (factored_eq_middleFour A C B D).symm

/-- Only centrality is needed for this order comparison. -/
theorem middleFour_tensorSequence {X Y A B : τ} {f : Obj X ⟶ Obj A} {g : Obj Y ⟶ Obj B}
    (hf : WhiskerCentral f) (hg : WhiskerCentral g) :
    middleFour X X Y Y ≫ ((f ⊗ₛ g) ⊗ₛ (f ⊗ₛ g)) =
      ((f ⊗ₛ f) ⊗ₛ (g ⊗ₛ g)) ≫ middleFour A A B B := by
  rw [← factored_eq_middleFour, ← factored_eq_middleFour]
  exact (factored_natural f g hf hg hg).symm

theorem centralCopies_pair {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : CentralCopies f) (hg : CentralCopies g) : CentralCopies (pairArrows f g) := by
  apply centralCopies_pair_of_shared_input_shuffle hf hg
  rw [Category.assoc, middleFour_tensorSequence hf.1 hg.1, Category.assoc]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MiddleFourInterchange
