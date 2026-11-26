module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

/-! # Syntactic elimination of one-way structured joins -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.GuardedJoin

open Silmaril.Isotope.LambdaSSA
open Region
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {A : τ}

private theorem renameGuardedLabels {b : Region Φ} {K : LCtx τ} {ρ : Nat → Nat}
    (hb : ValueBranches Γ b L) (hρ : Ren L K ρ) :
    ValueBranches Γ (b.renameLabels ρ) K := by
  rw [renameLabels_eq_lsubst]
  exact hb.lsubst (fun _ _ hi => .br (hρ hi) (.var rfl))

private theorem reentry {b : Region Φ} (hb : ValueBranches (A :: Γ) b L) :
    Paper.Eqv (A :: Γ) (CfgEta.reentry (b.renameLabels Nat.succ) 0) b L := by
  let block := (b.renameLabels Nat.succ).renameVars (lift Nat.succ)
  let R : Fin 1 → τ := fun _ => A
  have hblock : ∀ i, HasType (R i :: A :: Γ) block (List.ofFn R ++ L) := by
    intro i
    simpa only [R, List.ofFn_succ, List.ofFn_zero, List.nil_append, List.cons_append] using
      ((renameGuardedLabels hb (Ren.wk L A)).renameVars ((Ren.wk Γ A).lift A)).hasType
  have enter : SubstitutionEquiv (A :: Γ)
      (CfgEta.reentry (b.renameLabels Nat.succ) 0)
      (.cfg (.let₁ (.var 0) block) 1 (fun _ => block)) L :=
    .base (.entry (.cfgBrLocal R ⟨0, Nat.zero_lt_succ 0⟩ (.var rfl) hblock))
  have weakened := hb.renameVars ((Ren.wk Γ A).lift A)
  have hlet : HasType (A :: Γ) (.let₁ (.var 0) (b.renameVars (lift Nat.succ))) L :=
    .let₁ (.var rfl) weakened.hasType
  have drop : SubstitutionEquiv (A :: Γ)
      (.cfg (.let₁ (.var 0) block) 1 (fun _ => block))
      (.let₁ (.var 0) (b.renameVars (lift Nat.succ))) L := by
    have expand := SubstitutionEquiv.cfgOutward R hlet hblock
    simp only [renameLabels, Nat.zero_add, Nat.one_add, ← renameVars_renameLabels] at expand
    exact expand
  have varSubst : Tm.singleSubst (Tm.var 0 : Tm Φ) ∘ lift Nat.succ = Tm.var := by
    funext i
    cases i <;> rfl
  have beta : SubstitutionEquiv (A :: Γ)
      (.let₁ (.var 0) (b.renameVars (lift Nat.succ))) b L := by
    simpa only [substVars_renameVars, varSubst, substVars_var] using
      (SubstitutionEquiv.letValue (.var (i := 0) rfl) weakened.hasType)
  exact .cfgEta (.native (enter.trans (drop.trans beta)))

theorem link {entry block : Region Φ}
    (he : ValueBranches Γ entry [A]) (hb : ValueBranches (A :: Γ) block L) :
    Paper.Eqv Γ (CfgEta.singleCfg entry (block.renameLabels Nat.succ))
      (entry.lsubst (fun _ => block)) L := by
  have widen : Ren [A] (A :: L) id := by
    intro i B hi
    cases i with
    | zero => exact hi
    | succ i => simp [At] at hi
  have he' : ValueBranches Γ entry (A :: L) := by
    simpa only [renameLabels_id] using renameGuardedLabels he widen
  apply Paper.Eqv.trans (.cfgEta (CfgEta.Eqv.eta he' (renameGuardedLabels hb (Ren.wk L A))))
  apply Paper.Eqv.lsubstCongr he
  intro i B hi
  have zero : i = 0 := by simpa using (List.getElem?_eq_some_iff.mp hi).1
  subst i
  cases Option.some.inj hi
  exact reentry hb

end Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.GuardedJoin
