module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CopyStructure
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.MiddleSwap

/-! # Duplication and the product type former -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem action_copy {n : Nat} {Γ : QCtx τ n} {a : Term Φ n} {A : τ}
    (ha : HasType F Γ (⊥ : ε) a A) (hA : Quantity.relevant ≤ quantity A)
    (hqa : quantity A ≤ Γ.linearity) :
    Equates (ε := ε) F R Γ (action a (.pair (.bv 0) (.bv 0))) (.pair a a) (product A A) := by
  exact pureBetaTyped (R := R) (QCtx.Split.zero_right Γ) ha
    (atZeroDeriv Γ (copyDeriv A hA (⊤ : ε))) hqa

theorem tensorCopy_action {n : Nat} {Γ Γa Γb : QCtx τ n} {a b : Term Φ n} {A B : τ}
    (s : Γ.Split Γa Γb) (ha : HasType F Γa (⊥ : ε) a A)
    (hb : HasType F Γb (⊥ : ε) b B)
    (hA : Quantity.relevant ≤ quantity A) (hB : Quantity.relevant ≤ quantity B)
    (hqa : quantity A ≤ Γa.linearity) (hqb : quantity B ≤ Γb.linearity) :
    Equates (ε := ε) F R Γ
      (action (.pair a b)
        (composeTerm (rightTerm (.pair (.bv 0) (.bv 0))) (leftTerm (.pair (.bv 0) (.bv 0)))))
      (.pair (.pair a a) (.pair b b)) (product (product A A) (product B B)) := by
  have dca := copyDeriv (F := F) (Φ := Φ) A hA (⊤ : ε)
  have dcb := copyDeriv (F := F) (Φ := Φ) B hB (⊤ : ε)
  have daa := HasType.pair (QCtx.Split.diagonal Γa (hA.trans hqa)) ha ha
  have h₀ := action_compose (R := R) (HasType.pair s ha hb).top
    (rightDeriv B dca) (leftDeriv (product A A) dcb)
  have h₁ := (pair_then_right (R := R) s ha.top hb dca hqb).trans
    (Equates.pair s (action_copy (R := R) ha hA hqa) (Equates.refl ⟨hb.top⟩))
  have h₂ := (pair_then_left_any (R := R) s daa.top hb.top dcb).trans
    (Equates.pair s (Equates.refl ⟨daa.top⟩) (action_copy (R := R) hb hB hqb))
  exact h₀.trans ((action_congr h₁ (leftDeriv (product A A) dcb)).trans h₂)

theorem copy_product_equates (A B : τ) (hA : Quantity.relevant ≤ quantity A)
    (hB : Quantity.relevant ≤ quantity B) (hAB : Quantity.relevant ≤ quantity (product A B)) :
    Equates (ε := ε) F R (input (product A B))
      (.pair (.bv 0) (.bv 0))
      (composeTerm
        (composeTerm (rightTerm (.pair (.bv 0) (.bv 0))) (leftTerm (.pair (.bv 0) (.bv 0))))
        middleSwapTerm)
      (product (product A B) (product A B)) := by
  have df := copyDeriv (F := F) (Φ := Φ) (product A B) hAB (⊤ : ε)
  have dc := composeDeriv (rightDeriv B (copyDeriv (F := F) (Φ := Φ) A hA (⊤ : ε)))
    (leftDeriv (product A A) (copyDeriv B hB (⊤ : ε)))
  have dm := middleSwapDeriv (F := F) (Φ := Φ) A A B B (⊤ : ε)
  apply pair_ext df (composeDeriv dc dm)
  let P := product A B
  have s := pairSplit P A B
  have da := leftParameter (F := F) (Φ := Φ) P A B (⊥ : ε)
  have db := rightParameter (F := F) (Φ := Φ) P A B (⊥ : ε)
  have qa : quantity A ≤ (pairLeftContext P A B).linearity := by
    apply QCtx.le_linearity_iff.mpr; intro i
    fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top
  have qb : quantity B ≤ (pairRightContext P A B).linearity := by
    apply QCtx.le_linearity_iff.mpr; intro i
    fin_cases i <;> first | exact le_top | exact le_inf le_rfl le_top
  have qab : quantity (product A B) ≤ (pairContext P A B).linearity := by
    rw [TypeQuantity.product_quantity]
    exact s.le_linearity (inf_le_left.trans qa) (inf_le_right.trans qb)
  have hl := action_copy (R := R) (HasType.pair s da db) hAB qab
  have h₀ := action_compose (R := R) (HasType.pair s da db).top dc dm
  have h₁ := action_congr (tensorCopy_action (R := R) s da db hA hB qa qb) dm
  have h₂ := middleSwap_action (R := R) s
    (QCtx.Split.diagonal _ (hA.trans qa)) (QCtx.Split.diagonal _ (hB.trans qb))
    da da db db qa qa qb qb
  exact hl.trans (h₀.trans (h₁.trans h₂)).symm

theorem copy_product (hR : R.RenamingClosed) (A B : τ)
    (hA : Quantity.relevant ≤ quantity A) (hB : Quantity.relevant ≤ quantity B)
    (hAB : Quantity.relevant ≤ quantity (product A B)) :
    copy (ε := ε) (F := F) (R := R) (product A B) hAB =
      compose hR (compose hR (right hR (copy A hA) B) (left hR (product A A) (copy B hB)))
        (middleSwap A A B B) :=
  Quotient.sound (copy_product_equates A B hA hB hAB)

end Silmaril.Isotope.Refinement.Models.Syntactic
