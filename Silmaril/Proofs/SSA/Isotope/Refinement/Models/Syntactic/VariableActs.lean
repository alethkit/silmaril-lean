module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.SplitActs
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.UnitActs

/-! # Reification of structural variables and context discard -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless Denotation

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem discard_acts (hR : R.RenamingClosed) {n : Nat} {Γ : QCtx τ n}
    (hΓ : Γ.DefaultAnnotations) (hd : Γ.Discardable) :
    Acts Γ (packTerm Γ) (Denotation.discard (seqData (ε := ε) (F := F) (R := R) hR) hd) .unit := by
  simp only [Denotation.discard, seqData_discard]
  exact Acts.discard (R := R) (packDeriv Γ (⊥ : ε)) (discardable_quantity hd) (packed_quantity_eq hΓ).le

theorem variable_acts (hR : R.RenamingClosed) {n : Nat} {Γ : QCtx τ n}
    (hΓ : Γ.DefaultAnnotations) (i : Fin n) (hi : Γ.VarAllowed i) :
    Acts Γ (packTerm Γ) (Denotation.variable (seqData (ε := ε) (F := F) (R := R) hR) i hi) (.bv i) := by
  let M := seqData (ε := ε) (F := F) (R := R) hR
  induction Γ using QCtx.inductionOn with
  | nil => exact Fin.elim0 i
  | @snoc n Γ A q ih =>
    cases i using Fin.cases with
    | zero =>
      have ht : Γ.Discardable := fun j => hi.2 j.succ (Fin.succ_ne_zero _)
      have hq : q = .used ⊤ := by
        rcases hΓ 0 with hz | hq
        · change q = .zero at hz
          subst q
          exact False.elim hi.1
        · exact hq
      subst q
      have hp := (discard_acts (F := F) (R := R) (ε := ε) hR hΓ.tail ht).rename hR
        Fin.succ (.insertZero Γ A)
      have dp := (packDeriv (F := F) (Φ := Φ) Γ (⊥ : ε)).rename Fin.succ (.insertZero Γ A)
      have dv := zeroParameter (F := F) (Φ := Φ) Γ A (.used ⊤) (⊥ : ε) (by
        change Quantity.linear ⊓ quantity A ≤ ⊤ ⊓ quantity A
        exact inf_le_inf bot_le le_rfl)
      have s := (QCtx.Split.zero_right Γ).snoc (A := A) (.right (.used ⊤))
      have h₀ := hp.right hR s dp.top dv (zero_parameter_bound Γ A)
      have h₁ := Acts.leftUnit_variable (F := F) (R := R) (ε := ε) hR hΓ 0 hi
      have hall := h₀.compose hR (HasType.pair s dp dv).top h₁
      change Acts (Γ.snoc A) (.pair (packTerm Γ).lift (.bv 0))
        (M.compose (M.right (Denotation.discard M ht) A) (M.leftUnitor A)) (.bv 0)
      simp only [M, Denotation.discard, seqData_discard, seqData_right, seqData_leftUnitor,
        seqData_compose] at hall ⊢
      exact hall
    | succ i =>
      have ht : Γ.VarAllowed i :=
        ⟨hi.1, fun j hj => hi.2 j.succ (fun he => hj (Fin.succ_injective _ he))⟩
      have hz := hi.2 0 (Ne.symm (Fin.succ_ne_zero i))
      have hit := (ih hΓ.tail i ht).rename hR Fin.succ (.insertZero Γ A)
      rcases hΓ 0 with hq | hq
      · change q = .zero at hq
        subst q
        change Acts (Γ.snoc A .zero) (packTerm Γ).lift (Denotation.variable M i ht) (.bv i.succ)
        simpa only [Tm.rename, Tm.lift] using hit
      · change q = .used ⊤ at hq
        subst q
        have hA : Quantity.affine ≤ quantity A := by
          exact (Usage.zero_le_used _).mp hz
        have dp := (packDeriv (F := F) (Φ := Φ) Γ (⊥ : ε)).rename Fin.succ (.insertZero Γ A)
        have di := (HasType.var (F := F) (Φ := Φ) (e := (⊥ : ε)) i ht).rename Fin.succ (.insertZero Γ A)
        have dv := zeroParameter (F := F) (Φ := Φ) Γ A (.used ⊤) (⊥ : ε) (by
          change Quantity.linear ⊓ quantity A ≤ ⊤ ⊓ quantity A
          exact inf_le_inf bot_le le_rfl)
        have s := (QCtx.Split.zero_right Γ).snoc (A := A) (.right (.used ⊤))
        have h₀ := hit.right hR s dp.top dv (zero_parameter_bound Γ A)
        have h₁ := (Acts.discard (R := R) dv hA (zero_parameter_bound Γ A)).left hR s di.top dv.top
        have h₂ := Acts.rightUnit_variable (F := F) (R := R) (ε := ε) hR hΓ i.succ hi
        have hr := h₁.compose hR (HasType.pair s di dv).top h₂
        have hall := h₀.compose hR (HasType.pair s dp dv).top hr
        have heRight := seqData_right (ε := ε) (F := F) (R := R) hR
          (Denotation.variable (seqData hR) i ht) A
        change Acts (Γ.snoc A) (.pair (packTerm Γ).lift (.bv 0))
          (M.compose (M.right (Denotation.variable M i ht) A)
            (M.compose (M.left (Γ i).1 (M.discard A hA)) (M.rightUnitor (Γ i).1))) (.bv i.succ)
        simp only [M, seqData_discard, heRight, seqData_left, seqData_rightUnitor, seqData_compose] at hall ⊢
        exact hall

end Silmaril.Isotope.Refinement.Models.Syntactic
