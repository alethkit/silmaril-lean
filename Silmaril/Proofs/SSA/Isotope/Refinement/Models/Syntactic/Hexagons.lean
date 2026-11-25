module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.HexagonAction

/-! # Both native braiding hexagon equations -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem hexagon_forward_equates (A B C : τ) :
    Equates (ε := ε) F R (input (product (product A B) C))
      (composeTerm assocTerm (composeTerm swapTerm assocTerm))
      (composeTerm (rightTerm swapTerm) (composeTerm assocTerm (leftTerm swapTerm)))
      (product B (product C A)) := by
  apply triple_ext_left
    (composeDeriv (assocDeriv A B C (⊤ : ε))
      (composeDeriv (swapDeriv A (product B C) (⊤ : ε)) (assocDeriv B C A (⊤ : ε))))
    (composeDeriv (rightDeriv C (swapDeriv A B (⊤ : ε)))
      (composeDeriv (assocDeriv B A C (⊤ : ε)) (leftDeriv B (swapDeriv A C (⊤ : ε)))))
  let P := product (product A B) C
  let Γa : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A B) .zero).snoc C .zero).snoc A).snoc B .zero
  let Γb : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A B) .zero).snoc C .zero).snoc A .zero).snoc B
  let Γc : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A B) .zero).snoc C).snoc A .zero).snoc B .zero
  have da := singleVariable (F := F) (Φ := Φ) Γa 1 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have db := singleVariable (F := F) (Φ := Φ) Γb 0 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have dc := singleVariable (F := F) (Φ := Φ) Γc 2 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have qa : quantity A ≤ Γa.linearity := by
    apply QCtx.le_linearity_iff.mpr; intro i
    fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top
  have qb : quantity B ≤ Γb.linearity := by
    apply QCtx.le_linearity_iff.mpr; intro i
    fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top
  have qc : quantity C ≤ Γc.linearity := by
    apply QCtx.le_linearity_iff.mpr; intro i
    fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top
  have hl := hexagon_forward_action_left (R := R)
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.right (.used ⊤))).snoc (.left (.used ⊤))).snoc (.left (.used ⊤)))
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.left .zero)).snoc (.left (.used ⊤))).snoc (.right (.used ⊤))) da db dc qa qb qc
  have hr := hexagon_forward_action_right (R := R)
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.right (.used ⊤))).snoc (.left (.used ⊤))).snoc (.left (.used ⊤)))
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.left .zero)).snoc (.left (.used ⊤))).snoc (.right (.used ⊤))) da db dc qa qb qc
  exact hl.trans hr.symm

theorem hexagon_reverse_equates (A B C : τ) :
    Equates (ε := ε) F R (input (product A (product B C)))
      (composeTerm assocInvTerm (composeTerm swapTerm assocInvTerm))
      (composeTerm (leftTerm swapTerm) (composeTerm assocInvTerm (rightTerm swapTerm)))
      (product (product C A) B) := by
  apply triple_ext_right
    (composeDeriv (assocInvDeriv A B C (⊤ : ε))
      (composeDeriv (swapDeriv (product A B) C (⊤ : ε)) (assocInvDeriv C A B (⊤ : ε))))
    (composeDeriv (leftDeriv A (swapDeriv B C (⊤ : ε)))
      (composeDeriv (assocInvDeriv A C B (⊤ : ε)) (rightDeriv B (swapDeriv A C (⊤ : ε)))))
  let P := product A (product B C)
  let Γa : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc A).snoc (product B C) .zero).snoc B .zero).snoc C .zero
  let Γb : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc A .zero).snoc (product B C) .zero).snoc B).snoc C .zero
  let Γc : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc A .zero).snoc (product B C) .zero).snoc B .zero).snoc C
  have da := singleVariable (F := F) (Φ := Φ) Γa 3 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have db := singleVariable (F := F) (Φ := Φ) Γb 1 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have dc := singleVariable (F := F) (Φ := Φ) Γc 0 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have qa : quantity A ≤ Γa.linearity := by
    apply QCtx.le_linearity_iff.mpr; intro i
    fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top
  have qb : quantity B ≤ Γb.linearity := by
    apply QCtx.le_linearity_iff.mpr; intro i
    fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top
  have qc : quantity C ≤ Γc.linearity := by
    apply QCtx.le_linearity_iff.mpr; intro i
    fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top
  have hl := hexagon_reverse_action_left (R := R)
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left (.used ⊤))).snoc
      (.left .zero)).snoc (.right (.used ⊤))).snoc (.right (.used ⊤)))
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.left .zero)).snoc (.left (.used ⊤))).snoc (.right (.used ⊤))) da db dc qa qb qc
  have hr := hexagon_reverse_action_right (R := R)
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left (.used ⊤))).snoc
      (.left .zero)).snoc (.right (.used ⊤))).snoc (.right (.used ⊤)))
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.left .zero)).snoc (.left (.used ⊤))).snoc (.right (.used ⊤))) da db dc qa qb qc
  exact hl.trans hr.symm

theorem hexagon_forward (hR : R.RenamingClosed) (A B C : τ) :
    compose (ε := ε) (F := F) (R := R) hR (assoc A B C)
      (compose hR (swap A (product B C)) (assoc B C A)) =
    compose hR (right hR (swap A B) C)
      (compose hR (assoc B A C) (left hR B (swap A C))) :=
  Quotient.sound (hexagon_forward_equates A B C)

theorem hexagon_reverse (hR : R.RenamingClosed) (A B C : τ) :
    compose (ε := ε) (F := F) (R := R) hR (assocInv A B C)
      (compose hR (swap (product A B) C) (assocInv C A B)) =
    compose hR (left hR A (swap B C))
      (compose hR (assocInv A C B) (right hR (swap A C) B)) :=
  Quotient.sound (hexagon_reverse_equates A B C)

end Silmaril.Isotope.Refinement.Models.Syntactic
