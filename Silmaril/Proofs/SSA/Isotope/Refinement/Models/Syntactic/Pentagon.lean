module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.PentagonAction
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.QuadrupleExtensionality

/-! # The native associativity pentagon -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem pentagon_equates (A B C D : τ) :
    Equates (ε := ε) F R (input (product (product (product A B) C) D))
      (composeTerm (rightTerm assocTerm) (composeTerm assocTerm (leftTerm assocTerm)))
      (composeTerm assocTerm assocTerm) (product A (product B (product C D))) := by
  apply quadruple_ext_left
    (composeDeriv (rightDeriv D (assocDeriv A B C (⊤ : ε)))
      (composeDeriv (assocDeriv A (product B C) D (⊤ : ε))
        (leftDeriv A (assocDeriv B C D (⊤ : ε)))))
    (composeDeriv (assocDeriv (product A B) C D (⊤ : ε))
      (assocDeriv A B (product C D) (⊤ : ε)))
  let P := product (product (product A B) C) D
  let Ω := (QCtx.nil.snoc P .zero).snoc (product (product A B) C) .zero
  let Γa : QCtx τ 7 := ((((Ω.snoc D .zero).snoc (product A B) .zero).snoc C .zero).snoc A).snoc B .zero
  let Γb : QCtx τ 7 := ((((Ω.snoc D .zero).snoc (product A B) .zero).snoc C .zero).snoc A .zero).snoc B
  let Γc : QCtx τ 7 := ((((Ω.snoc D .zero).snoc (product A B) .zero).snoc C).snoc A .zero).snoc B .zero
  let Γd : QCtx τ 7 := ((((Ω.snoc D).snoc (product A B) .zero).snoc C .zero).snoc A .zero).snoc B .zero
  have da := singleVariable (F := F) (Φ := Φ) Γa 1 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have db := singleVariable (F := F) (Φ := Φ) Γb 0 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have dc := singleVariable (F := F) (Φ := Φ) Γc 2 (⊥ : ε) rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have dd := singleVariable (F := F) (Φ := Φ) Γd 4 (⊥ : ε) rfl
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
  have qd : quantity D ≤ Γd.linearity := by
    apply QCtx.le_linearity_iff.mpr; intro i
    fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top
  have hl := pentagon_action_long (R := R)
    (((((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.right (.used ⊤))).snoc (.left .zero)).snoc (.left (.used ⊤))).snoc
      (.left (.used ⊤))).snoc (.left (.used ⊤)))
    (((((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.left .zero)).snoc (.left .zero)).snoc (.right (.used ⊤))).snoc
      (.left (.used ⊤))).snoc (.left (.used ⊤)))
    (((((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.left .zero)).snoc (.left .zero)).snoc (.left .zero)).snoc
      (.left (.used ⊤))).snoc (.right (.used ⊤))) da db dc dd qa qb qc qd
  have hr := pentagon_action_short (R := R)
    (((((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.right (.used ⊤))).snoc (.left .zero)).snoc (.left (.used ⊤))).snoc
      (.left (.used ⊤))).snoc (.left (.used ⊤)))
    (((((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.left .zero)).snoc (.left .zero)).snoc (.right (.used ⊤))).snoc
      (.left (.used ⊤))).snoc (.left (.used ⊤)))
    (((((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.left .zero)).snoc (.left .zero)).snoc (.left .zero)).snoc
      (.left (.used ⊤))).snoc (.right (.used ⊤))) da db dc dd qa qb qc qd
  exact hl.trans hr.symm

theorem pentagon (hR : R.RenamingClosed) (A B C D : τ) :
    compose (ε := ε) (F := F) (R := R) hR (right hR (assoc A B C) D)
      (compose hR (assoc A (product B C) D) (left hR A (assoc B C D))) =
    compose hR (assoc (product A B) C D) (assoc A B (product C D)) :=
  Quotient.sound (pentagon_equates A B C D)

end Silmaril.Isotope.Refinement.Models.Syntactic
