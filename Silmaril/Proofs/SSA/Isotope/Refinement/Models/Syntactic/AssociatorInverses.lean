module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.AssociatorPairs
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.PairElimination
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Exchange

/-! # The native associator is invertible -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem nested_pair_eta_left (P A B C : τ) :
    Equates (ε := ε) F R (pairContext P (product A B) C)
      (.let₂ (.bv 1) (.pair (.pair (.bv 1) (.bv 0)) (.bv 2)) : Term Φ 3)
      (.pair (.bv 1) (.bv 0)) (product (product A B) C) := by
  let Γl := pairLeftContext P (product A B) C
  let Γr := pairRightContext P (product A B) C
  have hd := leftParameter (F := F) (Φ := Φ) P (product A B) C (⊤ : ε)
  have he := pair_let₂_left (R := R) (pairSplit P (product A B) C).symm
    (QCtx.Split.zero_right Γr) hd (pairVariables Γr A B (⊤ : ε))
    (rightParameter P (product A B) C (⊥ : ε))
  have heta := Equates.ofAxiom (R := R) (.pairEta hd)
    ⟨.let₂ (QCtx.Split.zero_left Γl) hd (pairVariables Γl A B (⊤ : ε))⟩ ⟨hd⟩
  exact he.symm.trans (Equates.pair (pairSplit P (product A B) C) heta
    (Equates.refl ⟨(rightParameter P (product A B) C (⊥ : ε)).top⟩))

theorem nested_pair_eta_right (P A B C : τ) :
    Equates (ε := ε) F R (pairContext P A (product B C))
      (.let₂ (.bv 0) (.pair (.bv 3) (.pair (.bv 1) (.bv 0))) : Term Φ 3)
      (.pair (.bv 1) (.bv 0)) (product A (product B C)) := by
  let Γl := pairLeftContext P A (product B C)
  let Γr := pairRightContext P A (product B C)
  have hd := rightParameter (F := F) (Φ := Φ) P A (product B C) (⊤ : ε)
  have he := pair_let₂_right (R := R) (pairSplit P A (product B C))
    (QCtx.Split.zero_right Γl) hd (pairVariables Γl B C (⊤ : ε))
    (leftParameter P A (product B C) (⊥ : ε))
  have heta := Equates.ofAxiom (R := R) (.pairEta hd)
    ⟨.let₂ (QCtx.Split.zero_left Γr) hd (pairVariables Γr B C (⊤ : ε))⟩ ⟨hd⟩
  exact he.symm.trans (Equates.pair (pairSplit P A (product B C))
    (Equates.refl ⟨(leftParameter P A (product B C) (⊥ : ε)).top⟩) heta)

/-- Reassociation followed by inverse reassociation is product eta, twice. -/
theorem assoc_assocInv_equates (A B C : τ) :
    Equates (ε := ε) F R (input (product (product A B) C))
      (composeTerm (assocTerm : Term Φ 1) assocInvTerm) (.bv 0)
      (product (product A B) C) := by
  let P := product (product A B) C
  let Δ := pairRightContext P (product A B) C
  let Γa : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A B) .zero).snoc C .zero).snoc A).snoc B .zero
  let Γb : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A B) .zero).snoc C .zero).snoc A .zero).snoc B
  let Γc : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A B) .zero).snoc C).snoc A .zero).snoc B .zero
  have da := singleVariable (F := F) (Φ := Φ) Γa 1 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have db := singleVariable (F := F) (Φ := Φ) Γb 0 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have dc := singleVariable (F := F) (Φ := Φ) Γc 2 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have hp := assocInv_pair_equates (R := R)
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.right (.used ⊤))).snoc (.left (.used ⊤))).snoc (.right (.used ⊤)))
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.right (.used ⊤))).snoc (.left .zero)).snoc (.left (.used ⊤))) da db dc
    (by change quantity A ≤ Γa.linearity
        apply QCtx.le_linearity_iff.mpr
        intro i
        fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top)
    (by change quantity B ≤ Γb.linearity
        apply QCtx.le_linearity_iff.mpr
        intro i
        fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top)
    (by change quantity C ≤ Γc.linearity
        apply QCtx.le_linearity_iff.mpr
        intro i
        fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top)
  have hmove := let_pair (R := R) (pairSplit P (product A B) C).symm
    (QCtx.Split.zero_left Δ) (leftParameter P (product A B) C (⊤ : ε))
    ((assocBodyDeriv (F := F) (Φ := Φ) A B C (⊤ : ε)).let₂View.body)
    (atZeroDeriv Δ (assocInvDeriv A B C (⊤ : ε)))
  have hbody : Equates (ε := ε) F R (pairContext P (product A B) C)
      (.let₁ (.let₂ (.bv 1) (.pair (.bv 1) (.pair (.bv 0) (.bv 2))))
        (atIndex 0 (assocInvTerm : Term Φ 1))) (.pair (.bv 1) (.bv 0)) P := by
    apply hmove.trans
    simp only [underBinder_atIndex_zero]
    exact (Equates.let₂ (pairSplit P (product A B) C).symm
      (Equates.refl ⟨leftParameter P (product A B) C (⊤ : ε)⟩) hp).trans
      (nested_pair_eta_left P A B C)
  have hP : (QCtx.nil.snoc P .zero).Discardable := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact le_rfl
  exact (destruct_compose (assocBodyDeriv A B C (⊤ : ε)) (assocInvDeriv A B C (⊤ : ε))).trans
    ((Equates.let₂ (inputSplit P) (Equates.refl ⟨identityDeriv P (⊤ : ε)⟩) hbody).trans
      (Equates.ofAxiom (.pairEta (identityDeriv P (⊤ : ε)))
        ⟨.let₂ (inputSplit P) (identityDeriv P (⊤ : ε))
          (parametersDeriv _ hP (product A B) C (⊤ : ε))⟩ ⟨identityDeriv P (⊤ : ε)⟩))

/-- The other inverse law uses the same native reductions in the opposite product shape. -/
theorem assocInv_assoc_equates (A B C : τ) :
    Equates (ε := ε) F R (input (product A (product B C)))
      (composeTerm (assocInvTerm : Term Φ 1) assocTerm) (.bv 0)
      (product A (product B C)) := by
  let P := product A (product B C)
  let Δ := pairLeftContext P A (product B C)
  let Γa : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc A).snoc (product B C) .zero).snoc B .zero).snoc C .zero
  let Γb : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc A .zero).snoc (product B C) .zero).snoc B).snoc C .zero
  let Γc : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc A .zero).snoc (product B C) .zero).snoc B .zero).snoc C
  have da := singleVariable (F := F) (Φ := Φ) Γa 3 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have db := singleVariable (F := F) (Φ := Φ) Γb 1 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have dc := singleVariable (F := F) (Φ := Φ) Γc 0 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have hp := assoc_pair_equates (R := R)
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left (.used ⊤))).snoc
      (.left .zero)).snoc (.left (.used ⊤))).snoc (.right (.used ⊤)))
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left (.used ⊤))).snoc
      (.left .zero)).snoc (.right (.used ⊤))).snoc (.left .zero)) da db dc
    (by change quantity A ≤ Γa.linearity
        apply QCtx.le_linearity_iff.mpr
        intro i
        fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top)
    (by change quantity B ≤ Γb.linearity
        apply QCtx.le_linearity_iff.mpr
        intro i
        fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top)
    (by change quantity C ≤ Γc.linearity
        apply QCtx.le_linearity_iff.mpr
        intro i
        fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top)
  have hmove := let_pair (R := R) (pairSplit P A (product B C))
    (QCtx.Split.zero_left Δ) (rightParameter P A (product B C) (⊤ : ε))
    ((assocInvBodyDeriv (F := F) (Φ := Φ) A B C (⊤ : ε)).let₂View.body)
    (atZeroDeriv Δ (assocDeriv A B C (⊤ : ε)))
  have hbody : Equates (ε := ε) F R (pairContext P A (product B C))
      (.let₁ (.let₂ (.bv 0) (.pair (.pair (.bv 3) (.bv 1)) (.bv 0)))
        (atIndex 0 (assocTerm : Term Φ 1))) (.pair (.bv 1) (.bv 0)) P := by
    apply hmove.trans
    simp only [underBinder_atIndex_zero]
    exact (Equates.let₂ (pairSplit P A (product B C))
      (Equates.refl ⟨rightParameter P A (product B C) (⊤ : ε)⟩) hp).trans
      (nested_pair_eta_right P A B C)
  have hP : (QCtx.nil.snoc P .zero).Discardable := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact le_rfl
  exact (destruct_compose (assocInvBodyDeriv A B C (⊤ : ε)) (assocDeriv A B C (⊤ : ε))).trans
    ((Equates.let₂ (inputSplit P) (Equates.refl ⟨identityDeriv P (⊤ : ε)⟩) hbody).trans
      (Equates.ofAxiom (.pairEta (identityDeriv P (⊤ : ε)))
        ⟨.let₂ (inputSplit P) (identityDeriv P (⊤ : ε))
          (parametersDeriv _ hP A (product B C) (⊤ : ε))⟩ ⟨identityDeriv P (⊤ : ε)⟩))

@[simp] theorem assoc_assocInv (hR : R.RenamingClosed) (A B C : τ) :
    compose (ε := ε) (F := F) (R := R) hR (assoc A B C) (assocInv A B C) =
      identity (product (product A B) C) :=
  Quotient.sound (assoc_assocInv_equates A B C)

@[simp] theorem assocInv_assoc (hR : R.RenamingClosed) (A B C : τ) :
    compose (ε := ε) (F := F) (R := R) hR (assocInv A B C) (assoc A B C) =
      identity (product A (product B C)) :=
  Quotient.sound (assocInv_assoc_equates A B C)

/-- The chosen associator is an isomorphism in the quantitative syntactic category. -/
def assocIso (hR : R.RenamingClosed) (A B C : τ) :
    letI := category (ε := ε) F R hR
    CategoryTheory.Iso (product (product A B) C) (product A (product B C)) := by
  letI := category (ε := ε) F R hR
  exact ⟨assoc A B C, assocInv A B C, assoc_assocInv hR A B C, assocInv_assoc hR A B C⟩

end Silmaril.Isotope.Refinement.Models.Syntactic
