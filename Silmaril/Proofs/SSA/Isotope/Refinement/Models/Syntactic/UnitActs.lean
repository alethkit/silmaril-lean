module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.StructuralActs

/-! # Unit coherence in ambient quantitative contexts -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

namespace Acts
variable {n : Nat} {Γ : QCtx τ n} {a : Term Φ n} {A : τ}

theorem leftUnit (hR : R.RenamingClosed) (ha : HasType F Γ (⊥ : ε) a A)
    (hq : quantity A ≤ Γ.linearity) :
    Acts Γ (.pair .unit a) (Syntactic.leftUnit (F := F) (R := R) (ε := ε) A) a := by
  have hi := Acts.identity (R := R) ha hq
  rw [← leftUnitInv_leftUnit hR A] at hi
  have hcomp := hi.representative hR ha.top (composeArrow (leftUnitInvArrow A) (leftUnitArrow A)) rfl
  have hin := (Acts.leftUnitInv (R := R) ha hq).representative hR ha.top (leftUnitInvArrow A) rfl
  have hc := action_compose (R := R) ha.top (leftUnitInvDeriv A (⊤ : ε)) (leftUnitDeriv A (⊤ : ε))
  have he := (action_congr hin (leftUnitDeriv A (⊤ : ε))).symm.trans (hc.symm.trans hcomp)
  exact of_equates (r := leftUnitArrow A) he

theorem rightUnit (hR : R.RenamingClosed) (ha : HasType F Γ (⊥ : ε) a A)
    (hq : quantity A ≤ Γ.linearity) :
    Acts Γ (.pair a .unit) (Syntactic.rightUnit (F := F) (R := R) (ε := ε) A) a := by
  have hi := Acts.identity (R := R) ha hq
  rw [← rightUnitInv_rightUnit hR A] at hi
  have hcomp := hi.representative hR ha.top (composeArrow (rightUnitInvArrow A) (rightUnitArrow A)) rfl
  have hin := (Acts.rightUnitInv (R := R) ha hq).representative hR ha.top (rightUnitInvArrow A) rfl
  have hc := action_compose (R := R) ha.top (rightUnitInvDeriv A (⊤ : ε)) (rightUnitDeriv A (⊤ : ε))
  have he := (action_congr hin (rightUnitDeriv A (⊤ : ε))).symm.trans (hc.symm.trans hcomp)
  exact of_equates (r := rightUnitArrow A) he

/-- Unit elimination around a selected variable remains valid even when its
ambient context contains additional affine resources. -/
theorem leftUnit_variable (hR : R.RenamingClosed) {n : Nat} {Γ : QCtx τ n}
    (hΓ : Γ.DefaultAnnotations) (i : Fin n) (hi : Γ.VarAllowed i) :
    Acts Γ (.pair .unit (.bv i)) (Syntactic.leftUnit (F := F) (R := R) (ε := ε) (Γ i).1) (.bv i) := by
  have h := Acts.leftUnit (R := R) hR (identityDeriv (F := F) (Φ := Φ) (Γ i).1 (⊥ : ε))
    (by rw [input_linearity])
  simpa only [Tm.rename] using h.rename hR (fun _ => i) (defaultVariableWeakening hΓ i hi)

theorem rightUnit_variable (hR : R.RenamingClosed) {n : Nat} {Γ : QCtx τ n}
    (hΓ : Γ.DefaultAnnotations) (i : Fin n) (hi : Γ.VarAllowed i) :
    Acts Γ (.pair (.bv i) .unit) (Syntactic.rightUnit (F := F) (R := R) (ε := ε) (Γ i).1) (.bv i) := by
  have h := Acts.rightUnit (R := R) hR (identityDeriv (F := F) (Φ := Φ) (Γ i).1 (⊥ : ε))
    (by rw [input_linearity])
  simpa only [Tm.rename] using h.rename hR (fun _ => i) (defaultVariableWeakening hΓ i hi)

end Acts
end Silmaril.Isotope.Refinement.Models.Syntactic
