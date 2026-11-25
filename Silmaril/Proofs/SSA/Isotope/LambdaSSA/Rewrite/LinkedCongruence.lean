module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Composition.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.ContinuationLaws

/-! # Native congruence of linked CFGs -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.SSA (Ren)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

private theorem substitutionEquiv_renameLabels {Γ : VCtx τ} {L K : LCtx τ} {ρ : Nat → Nat}
    {r s : Region Φ} (h : SubstitutionEquiv Γ r s L) (hρ : Ren L K ρ) :
    SubstitutionEquiv Γ (r.renameLabels ρ) (s.renameLabels ρ) K := by
  rw [renameLabels_eq_lsubst, renameLabels_eq_lsubst]
  exact h.lsubst fun _ _ hi => .br (hρ hi) (.var rfl)

theorem substitutionEquiv_linkExits {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : SubstitutionEquiv Γ r s L) {σ υ : Nat → Region Φ}
    (hσ : ∀ ⦃i A⦄, At L i A → SubstitutionEquiv (A :: Γ) (σ i) (υ i) K) :
    SubstitutionEquiv Γ (r.linkExits L σ) (s.linkExits L υ) K := by
  let R : Fin L.length → τ := L.get
  have hR : List.ofFn R = L := List.ofFn_get L
  have hin : Ren L (List.ofFn R ++ K) id := by
    intro i A hi
    simpa only [hR, id_eq, At, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1] using hi
  have hout : Ren K (List.ofFn R ++ K) (fun i => L.length + i) := by
    intro i A hi
    simpa [hR, At, List.getElem?_append_right] using hi
  refine .cfg R ?_ (fun i => ?_)
  · simpa only [renameLabels_id] using substitutionEquiv_renameLabels h hin
  · exact substitutionEquiv_renameLabels (hσ (show At L i (L.get i) by simp [At])) hout

theorem linkCompLSubst_congr {Γ : VCtx τ} {L K H : LCtx τ} {σ σ' υ υ' : Nat → Region Φ}
    (hσ : ∀ ⦃i A⦄, At L i A → SubstitutionEquiv (A :: Γ) (σ i) (σ' i) K)
    (hυ : ∀ ⦃i A⦄, At K i A → SubstitutionEquiv (A :: Γ) (υ i) (υ' i) H) :
    ∀ ⦃i A⦄, At L i A →
      SubstitutionEquiv (A :: Γ) (linkCompLSubst K σ υ i) (linkCompLSubst K σ' υ' i) H := by
  intro i A hi
  apply substitutionEquiv_linkExits (hσ hi)
  intro j B hj
  simp only [liftLSubstVars, renameVars_eq_substVars]
  exact (hυ hj).substVars (fun _ _ h => .var (((Ren.wk Γ A).lift B) h))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
