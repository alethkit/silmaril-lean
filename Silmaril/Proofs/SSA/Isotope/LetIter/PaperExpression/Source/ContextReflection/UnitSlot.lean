module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.UnitSlot.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms

/-! # Typed specialization and reconstruction at a pure unit slot -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection.UnitSlot.Proofs

universe u v w

variable {τ : Type u} {Φ : Type v} {ε : Type w}
variable {Γ : EffectCtx τ ε}

def retained (i : Nat) (j : Fin (eraseCtx Γ i).length) : Fin Γ.length :=
  ⟨insertIndex i j, by
    have hj := j.isLt
    by_cases h : j.val < i
    · simp only [insertIndex, ite_eq_left h]
      exact lt_of_lt_of_le hj (List.length_eraseIdx_le Γ i)
    · have hi : i < Γ.length := by
        have hlen := List.length_eraseIdx_le Γ i
        change j.val < (Γ.eraseIdx i).length at hj
        omega
      have hlen := List.length_eraseIdx_of_lt hi
      change j.val < (Γ.eraseIdx i).length at hj
      simp only [insertIndex, ite_eq_right h]
      omega⟩

theorem retained_get (i : Nat) (j : Fin (eraseCtx Γ i).length) :
    (eraseCtx Γ i).get j = Γ.get (retained i j) := by
  by_cases h : j.val < i
  · have he : (retained i j).val = j.val := by simp [retained, insertIndex, h]
    exact (List.getElem_eraseIdx_of_lt j.isLt h).trans
      (congrArg Γ.get (Fin.ext he.symm))
  · have he : (retained i j).val = j.val + 1 := by simp [retained, insertIndex, h]
    exact (List.getElem_eraseIdx_of_ge j.isLt (Nat.le_of_not_gt h)).trans
      (congrArg Γ.get (Fin.ext he.symm))

section Source

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
variable {a b : Expr Φ} {C : τ} {e : ε}

omit [TypeFormers τ] in
public theorem eraseCtx_pure (hΓ : Γ.Pure) (i : Nat) : (eraseCtx Γ i).Pure := by
  intro j
  rw [retained_get]
  exact hΓ (retained i j)

theorem eraseCtx_rename (i : Nat) (j : Fin (eraseCtx Γ i).length) :
    Wf Γ (.var (insertIndex i j) : Expr Φ) ((eraseCtx Γ i).get j).1
      ((eraseCtx Γ i).get j).2 := by
  rw [retained_get]
  exact Wf.var (retained i j) le_rfl

theorem unitSubst_typed (i : Fin Γ.length)
    (ht : (Γ.get i).1 = unit) (he : (Γ.get i).2 = ⊥) :
    ∀ j : Fin Γ.length, Wf (eraseCtx Γ i) (unitSubst i j.val : Expr Φ) (Γ.get j).1 (Γ.get j).2 := by
  intro j
  by_cases hj : j.val = i.val
  · obtain rfl := Fin.ext hj
    rw [ht, he]
    simpa [unitSubst] using Wf.unit (Φ := Φ) (eraseCtx Γ j) (⊥ : ε)
  · have hlen := List.length_eraseIdx_of_lt i.isLt
    have hjlt := j.isLt
    by_cases hlt : j.val < i.val
    · let k : Fin (eraseCtx Γ i).length := ⟨j.val, by change _ < (Γ.eraseIdx i).length; omega⟩
      have hk : (eraseCtx Γ i).get k = Γ.get j := List.getElem_eraseIdx_of_lt k.isLt hlt
      simpa only [unitSubst, ite_eq_right hj, ite_eq_left hlt, ← hk] using
        (Wf.var (Φ := Φ) (Γ := eraseCtx Γ i) k le_rfl)
    · let k : Fin (eraseCtx Γ i).length :=
        ⟨j.val - 1, by change _ < (Γ.eraseIdx i).length; omega⟩
      have hk : (eraseCtx Γ i).get k = Γ.get j := by
        have hge : i.val ≤ k.val := by change i.val ≤ j.val - 1; omega
        have hv : k.val + 1 = j.val := by change j.val - 1 + 1 = j.val; omega
        exact (List.getElem_eraseIdx_of_ge k.isLt hge).trans (congrArg Γ.get (Fin.ext hv))
      simpa only [unitSubst, ite_eq_right hj, ite_eq_right hlt, ← hk] using
        (Wf.var (Φ := Φ) (Γ := eraseCtx Γ i) k le_rfl)

public theorem unit_eta_rebuild (i : Fin Γ.length)
    (ht : (Γ.get i).1 = unit) (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) :
    Eqv Γ C e a (rebuildUnit i a) := by
  have hrel (j : Fin Γ.length) :
      Eqv Γ (Γ.get j).1 (Γ.get j).2 (.var j.val : Expr Φ)
        ((unitSubst i j.val).wk (insertIndex i)) := by
    by_cases hj : j.val = i.val
    · obtain rfl := Fin.ext hj
      have hw : Wf Γ (.var j.val : Expr Φ) unit (⊥ : ε) := by
        simpa only [ht] using Wf.var (Φ := Φ) j he.le
      rw [ht, he]
      simpa [unitSubst, Expr.wk] using Eqv.step (Step.terminal hw (Wf.unit Γ (⊥ : ε)))
    · have hidx : insertIndex i (if j.val < i.val then j.val else j.val - 1) = j.val := by
        unfold insertIndex
        split <;> first | rfl | (split <;> omega)
      simpa only [unitSubst, ite_eq_right hj, Expr.wk, hidx] using
        Eqv.refl (Wf.var (Φ := Φ) j le_rfl)
  simpa only [rebuildUnit, specializeUnit, Expr.wk_subst, Expr.subst_var] using
    ha.subst_congr (σ := Expr.var) (θ := fun j => (unitSubst i j).wk (insertIndex i)) hrel

public theorem wf_specializeUnit (i : Fin Γ.length) (ht : (Γ.get i).1 = unit)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) :
    Wf (eraseCtx Γ i) (specializeUnit i a) C e := ha.subst_typed (unitSubst_typed i ht he)

public theorem eqv_insertUnit (i : Fin Γ.length) (h : Eqv (eraseCtx Γ i) C e a b) :
    Eqv Γ C e (a.wk (insertIndex i)) (b.wk (insertIndex i)) :=
  h.wk_typed (eraseCtx_rename i)

public theorem eqv_iff_specializeUnit (i : Fin Γ.length) (ht : (Γ.get i).1 = unit)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) (hb : Wf Γ b C e) :
    Eqv Γ C e a b ↔ Eqv (eraseCtx Γ i) C e (specializeUnit i a) (specializeUnit i b) := by
  constructor
  · intro h
    exact h.subst_typed (unitSubst_typed i ht he)
  · intro h
    exact (unit_eta_rebuild i ht he ha).trans
      ((eqv_insertUnit i h).trans (unit_eta_rebuild i ht he hb).symm)

end Source

section Native

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
variable {a b : Expr Φ} {C : τ}

public theorem native_specializeUnit (i : Fin Γ.length) (hΓ : Γ.Pure) (hty : (Γ.get i).1 = unit)
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s)
    (h : AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) Γ.toBoundCtx t s C) :
    ∃ t' s' : Tm Empty Φ (eraseCtx Γ i).length,
      (specializeUnit i a).toLetIter (eraseCtx Γ i).length = some t' ∧
      (specializeUnit i b).toLetIter (eraseCtx Γ i).length = some s' ∧
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) (eraseCtx Γ i).toBoundCtx t' s' C :=
  Source.native_subst hΓ ht hs h (unitSubst_typed i hty (hΓ i))

end Native

end Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection.UnitSlot.Proofs
