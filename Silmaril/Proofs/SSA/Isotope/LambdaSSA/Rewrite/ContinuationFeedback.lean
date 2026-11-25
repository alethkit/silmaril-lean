module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Feedback.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueFamilies
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ClosureValues

/-! # Typing and congruence of syntactic CFG feedback -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L K : LCtx τ} {σ υ : Nat → Region Φ}

theorem feedbackRegion_valueFamily (h : LSubst.ValueFamily Γ L (L ++ K) σ) :
    LSubst.ValueFamily Γ L K (feedbackRegion L σ) := by
  intro i A hi
  let R : Fin L.length → τ := L.get
  have hR : List.ofFn R = L := List.ofFn_get L
  refine .cfg R (.br ?_ (.var rfl)) (fun j => ?_)
  · simpa only [hR, At, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1] using hi
  · have hj : At L j (R j) := by simp [R, At]
    rw [hR]
    exact valueFamily_liftVars h A hj

theorem feedbackRegion_congr
    (h : ∀ ⦃i A⦄, At L i A → SubstitutionEquiv (A :: Γ) (σ i) (υ i) (L ++ K)) :
    ∀ ⦃i A⦄, At L i A → SubstitutionEquiv (A :: Γ) (feedbackRegion L σ i) (feedbackRegion L υ i) K := by
  intro i A hi
  let R : Fin L.length → τ := L.get
  have hR : List.ofFn R = L := List.ofFn_get L
  refine .cfg R (.base (.refl (.br ?_ (.var rfl)))) (fun j => ?_)
  · simpa only [hR, At, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1] using hi
  · have hj : At L j (R j) := by simp [R, At]
    rw [hR]
    exact substitutionEquiv_liftLSubstVars h A hj

theorem feedbackRegion_unfold (h : LSubst.ValueFamily Γ L (L ++ K) σ) (i : Fin L.length) :
    SubstitutionEquiv (L.get i :: Γ) (feedbackRegion L σ i)
      (.cfg (σ i) L.length (fun j => (σ j).renameVars (lift Nat.succ))) K := by
  cases L with
  | nil => exact Fin.elim0 i
  | cons A L =>
    let R : Fin (A :: L).length → τ := (A :: L).get
    have hR : List.ofFn R = A :: L := List.ofFn_get _
    let blocks : Fin (A :: L).length → Region Φ := fun j => (σ j).renameVars (lift Nat.succ)
    have hb (j : Fin (A :: L).length) :
        HasType (R j :: R i :: Γ) (blocks j) (List.ofFn R ++ K) := by
      have hj : At (A :: L) j (R j) := by simp [At, R]
      rw [hR]
      exact (valueFamily_liftVars h (R i) hj).hasType
    refine (SubstitutionEquiv.base (.entry (.cfgBrLocal R i (.var (i := 0) rfl) hb))).trans ?_
    refine .cfg R ?_ (fun j => .base (.refl (hb j)))
    have eq : (blocks i).substVars (Tm.singleSubst (.var 0)) = σ i :=
      congrFun (compLSubst_id_left σ) i
    rw [← eq]
    exact .letValue (.var (i := 0) rfl) (hb i)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
