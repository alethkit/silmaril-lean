module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms
import Silmaril.Raw.SSA.Isotope.LambdaSSA.Substitution

/-! # Moving a pure case across a CFG binder -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.SSA (Ren)
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

private theorem weaken_single (r : Region Φ) (e : Tm Φ) :
    (r.renameVars (lift Nat.succ)).substVars (Tm.liftSubst (Tm.singleSubst e)) = r := by
  rw [substVars_renameVars]
  have h : Tm.liftSubst (Tm.singleSubst e) ∘ lift Nat.succ = Tm.var := by
    funext i
    cases i <;> rfl
  rw [h, substVars_var]

private theorem weaken_replace (r : Region Φ) (e : Tm Φ) :
    (r.renameVars (lift Nat.succ)).substVars (Tm.liftSubst (Tm.replaceNewest e)) =
      r.renameVars (lift Nat.succ) := by
  rw [substVars_renameVars, renameVars_eq_substVars]
  congr 1
  funext i
  cases i <;> rfl

private theorem weaken_single_var (r : Region Φ) :
    (r.renameVars (lift Nat.succ)).substVars (Tm.singleSubst (.var 0)) = r := by
  rw [substVars_renameVars]
  have h : Tm.singleSubst (.var (Φ := Φ) 0) ∘ lift Nat.succ = Tm.var := by
    funext i
    cases i <;> rfl
  rw [h, substVars_var]

private theorem cfg_arm {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (R : Fin n → τ) {blocks : Fin n → Region Φ} {A : τ}
    (h : SubstitutionEquiv (A :: Γ) r s (List.ofFn R ++ L))
    (hb : ∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    SubstitutionEquiv (A :: Γ)
      (.cfg r n (fun i => (blocks i).renameVars (lift Nat.succ)))
      (.cfg s n (fun i => (blocks i).renameVars (lift Nat.succ))) L :=
  .cfg R h (fun i => .base (.refl ((hb i).renameVars ((Ren.wk Γ A).lift (R i)))))

theorem cfg_caseValue {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {A B : τ}
    {e : Tm Φ} {l r : Region Φ} (R : Fin n → τ) {blocks : Fin n → Region Φ}
    (he : Tm.BranchValue Γ e (Silmaril.coprod A B))
    (hl : HasType (A :: Γ) l (List.ofFn R ++ L))
    (hr : HasType (B :: Γ) r (List.ofFn R ++ L))
    (hb : ∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    SubstitutionEquiv Γ (.cfg (.case e l r) n blocks)
      (.case e
        (.cfg l n (fun i => (blocks i).renameVars (lift Nat.succ)))
        (.cfg r n (fun i => (blocks i).renameVars (lift Nat.succ)))) L := by
  let S := Silmaril.coprod A B
  let l' := l.renameVars (lift Nat.succ)
  let r' := r.renameVars (lift Nat.succ)
  let b' (i : Fin n) := (blocks i).renameVars (lift Nat.succ)
  let k := Region.cfg (.case (.var 0) l' r') n b'
  have hk : HasType (S :: Γ) k L :=
    .cfg R (.case (.var rfl) (hl.renameVars ((Ren.wk Γ S).lift A))
      (hr.renameVars ((Ren.wk Γ S).lift B)))
      (fun i => (hb i).renameVars ((Ren.wk Γ S).lift (R i)))
  have hleft : SubstitutionEquiv (A :: Γ)
      (.case (.inl (.var 0)) l' r') l (List.ofFn R ++ L) := by
    have hl' := hl.renameVars ((Ren.wk Γ A).lift A)
    have hr' := hr.renameVars ((Ren.wk Γ A).lift B)
    apply SubstitutionEquiv.trans (.base (.caseInl (.var rfl) hl' hr'))
    simpa only [l', weaken_single_var] using SubstitutionEquiv.letValue (.var (i := 0) rfl) hl'
  have hright : SubstitutionEquiv (B :: Γ)
      (.case (.inr (.var 0)) l' r') r (List.ofFn R ++ L) := by
    have hl' := hl.renameVars ((Ren.wk Γ B).lift A)
    have hr' := hr.renameVars ((Ren.wk Γ B).lift B)
    apply SubstitutionEquiv.trans (.base (.caseInr (.var rfl) hl' hr'))
    simpa only [r', weaken_single_var] using SubstitutionEquiv.letValue (.var (i := 0) rfl) hr'
  have eta : SubstitutionEquiv Γ
      (.case e (.cfg (.case (.inl (.var 0)) l' r') n b')
        (.cfg (.case (.inr (.var 0)) l' r') n b'))
      (.cfg (.case e l r) n blocks) L := by
    simpa only [k, l', r', b', substVars, Tm.subst, weaken_replace, weaken_single,
      show ∀ a : Tm Φ, Tm.replaceNewest a 0 = a from fun _ => rfl,
      show ∀ a : Tm Φ, Tm.singleSubst a 0 = a from fun _ => rfl] using
      SubstitutionEquiv.caseValue he hk
  exact eta.symm.trans (.case he.hasType (cfg_arm R hleft hb) (cfg_arm R hright hb))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
