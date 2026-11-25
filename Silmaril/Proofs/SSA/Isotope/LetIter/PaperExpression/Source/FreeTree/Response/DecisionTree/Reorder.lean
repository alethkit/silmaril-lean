module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

/-! # Specializing and reordering pure-input decision trees -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree.Reorder.Proofs

open Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit (branchCtx caseArms replaceVar toFront)

universe u w

variable {α Φ : Type u} (S : Signature α Φ) {ε : Type w}
  [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {c : α}

private abbrev tagged (isLeft : Bool) (v : Expr Φ) : Expr Φ :=
  if isLeft then .inl v else .inr v

private abbrev specialize (isLeft : Bool) (i : Nat) (p : Expr Φ) : Expr Φ :=
  p.subst (replaceVar i (tagged isLeft (.var i)))

private theorem specialize_arm (isLeft : Bool) {i j : Nat} (hij : i ≠ j) (a : Expr Φ) :
    (a.wk (toFront j)).subst (Expr.liftSubst (replaceVar i (tagged isLeft (.var i)))) =
      (specialize isLeft i a).wk (toFront j) := by
  rw [Expr.subst_wk, Expr.wk_subst]
  congr 1
  funext k
  by_cases hj : k = j
  · subst k
    simp [toFront, Expr.liftSubst, replaceVar, hij.symm, Expr.wk]
  · by_cases hi : k = i
    · subst k
      cases isLeft <;>
        simp [tagged, toFront, Expr.liftSubst, replaceVar, Expr.wk0, Expr.wk, hij]
    · simp [toFront, Expr.liftSubst, replaceVar, hi, hj, Expr.wk0, Expr.wk]

private theorem specialize_case (isLeft : Bool) {i j : Nat} (hij : i ≠ j) (l r : Expr Φ) :
    specialize isLeft i (caseArms j l r) =
      caseArms j (specialize isLeft i l) (specialize isLeft i r) := by
  simp only [caseArms, Expr.subst, replaceVar, ite_eq_right hij.symm,
    specialize_arm isLeft hij]

private abbrev afterSplit (i j : Fin Γ.length) (T : Ty α) :
    Fin (branchCtx Γ i T).length :=
  j.cast List.length_set.symm

omit [HasEff Φ ε] in
private theorem lookup_afterSplit (i j : Fin Γ.length) (hij : i.val ≠ j.val) (T : Ty α) :
    (branchCtx Γ i T).get (afterSplit i j T) = Γ.get j :=
  List.getElem_set_ne hij _

omit [HasEff Φ ε] in
private theorem branchCtx_comm (i j : Fin Γ.length) (hij : i.val ≠ j.val) (T U : Ty α) :
    branchCtx (branchCtx Γ j U) (afterSplit j i U) T =
      branchCtx (branchCtx Γ i T) (afterSplit i j T) U :=
  List.set_comm (U, ⊥) (T, ⊥) hij.symm

private theorem specialize_program (e : ε) {shape : Shape Γ}
    (p : Program S c shape) (hp : Program.WellTyped S e p) (hΓ : Γ.Pure)
    (i : Fin Γ.length) {x y : α} (hi : (Γ.get i).1 = .coprod (.base x) (.base y))
    (isLeft : Bool) :
    letI := S.endpoints
    ∃ (shape' : Shape (branchCtx Γ i (.base (if isLeft then x else y))))
      (p' : Program S c shape'),
      Program.WellTyped S e p' ∧ Eqv (branchCtx Γ i (.base (if isLeft then x else y))) (.base c) e (specialize isLeft i p.source) p'.source := by
  let instr := S.endpoints
  induction p with
  | @leaf Γ slots hs p =>
    cases hi.symm.trans (hs i)
  | @split Γ j a b hj sl sr l r ihl ihr =>
    let Γl := branchCtx Γ j (.base a)
    let Γr := branchCtx Γ j (.base b)
    have hΓl : Γl.Pure := SumSplit.branchCtx_pure hΓ j (.base a)
    have hΓr : Γr.Pure := SumSplit.branchCtx_pure hΓ j (.base b)
    by_cases hij : i.val = j.val
    · obtain rfl := Fin.ext hij
      have hab := hi.symm.trans hj
      injection hab with ha hb
      injection ha with ha'
      injection hb with hb'
      subst a
      subst b
      have hl := DecisionTree.source_wf S hΓl e l hp.1
      have hr := DecisionTree.source_wf S hΓr e r hp.2
      cases isLeft
      · exact ⟨_, r, hp.2, SumSplit.caseArms_right i hi (hΓ i) hl hr⟩
      · exact ⟨_, l, hp.1, SumSplit.caseArms_left i hi (hΓ i) hl hr⟩
    · let T : Ty α := .base (if isLeft then x else y)
      let Δ := branchCtx Γ i T
      let j' := afterSplit i j T
      have hleft := lookup_afterSplit j i (Ne.symm hij) (.base a)
      have hright := lookup_afterSplit j i (Ne.symm hij) (.base b)
      have hL := ihl hp.1 hΓl (afterSplit j i (.base a))
        ((congrArg Prod.fst hleft).trans hi)
      have hR := ihr hp.2 hΓr (afterSplit j i (.base b))
        ((congrArg Prod.fst hright).trans hi)
      have hCl := branchCtx_comm i j hij T (.base a)
      have hCr := branchCtx_comm i j hij T (.base b)
      rw [hCl] at hL
      rw [hCr] at hR
      obtain ⟨sl', l', htl, el⟩ := hL
      obtain ⟨sr', r', htr, er⟩ := hR
      have hj' : (Δ.get j').1 = .coprod (.base a) (.base b) :=
        (congrArg Prod.fst (lookup_afterSplit i j hij T)).trans hj
      have hΔ := SumSplit.branchCtx_pure hΓ i T
      refine ⟨.split j' hj' sl' sr', .split j' l' r', ⟨htl, htr⟩, ?_⟩
      change Eqv Δ (.base c) e (specialize isLeft i.val (caseArms j.val l.source r.source))
        (caseArms j.val l'.source r'.source)
      rw [specialize_case isLeft hij]
      exact (SumSplit.caseArms_eqv_iff j' hj' (hΔ j') el.endpoints_wf.1 er.endpoints_wf.1
        el.endpoints_wf.2 er.endpoints_wf.2).mpr ⟨el, er⟩

public theorem normalize_to (hΓ : Γ.Pure) (e : ε) (target : Shape Γ)
    {shape : Shape Γ} (p : Program S c shape) (hp : Program.WellTyped S e p) :
    letI := S.endpoints
    ∃ q : Program S c target, Program.WellTyped S e q ∧ Eqv Γ (.base c) e p.source q.source := by
  let instr := S.endpoints
  induction target with
  | @leaf Γ slots hs =>
    cases p with
    | @leaf _ slots' hs' p =>
      have he : slots' = slots := funext fun i => Ty.base.inj ((hs' i).symm.trans (hs i))
      subst slots'
      exact ⟨.leaf p, hp, .refl (source_wf S hΓ e (.leaf p) hp)⟩
    | @split _ i _ _ hi _ _ _ _ =>
      cases hi.symm.trans (hs i)
  | @split Γ i x y hi l r ihl ihr =>
    have hΓl := SumSplit.branchCtx_pure hΓ i (.base x)
    have hΓr := SumSplit.branchCtx_pure hΓ i (.base y)
    obtain ⟨_, pL, hpL, epL⟩ := specialize_program S e p hp hΓ i hi true
    obtain ⟨_, pR, hpR, epR⟩ := specialize_program S e p hp hΓ i hi false
    obtain ⟨qL, hqL, el⟩ := ihl hΓl pL hpL
    obtain ⟨qR, hqR, er⟩ := ihr hΓr pR hpR
    have eL := epL.trans el
    have eR := epR.trans er
    refine ⟨.split i qL qR, ⟨hqL, hqR⟩, (SumSplit.eqv_rebuild i hi (hΓ i)
      (source_wf S hΓ e p hp)).trans ?_⟩
    exact (SumSplit.caseArms_eqv_iff i hi (hΓ i) eL.endpoints_wf.1 eR.endpoints_wf.1
      eL.endpoints_wf.2 eR.endpoints_wf.2).mpr ⟨eL, eR⟩

variable [EffectIteration ε] [DecidableEq α]

public theorem endpoint_reflection (hΓ : Γ.Pure) (e : ε) {shape other : Shape Γ}
    (p : Program S c shape) (q : Program S c other)
    (hp : Program.WellTyped S e p) (hq : Program.WellTyped S e q)
    {t s : Tm Empty Φ Γ.length}
    (ht : p.source.toLetIter Γ.length = some t) (hs : q.source.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base c) ↔
      Eqv Γ (.base c) e p.source q.source := by
  let instr := S.endpoints
  refine ⟨?_, fun h => h.toLetIter ht hs⟩
  intro h
  obtain ⟨q', hq', eq⟩ := normalize_to S hΓ e shape q hq
  obtain ⟨_, hs', _⟩ := eq.endpoints_wf.2.toLetIter
  have hn := h.trans (eq.toLetIter hs hs')
  exact ((DecisionTree.endpoint_reflection S hΓ e p q' hp hq' ht hs').mp hn).trans eq.symm

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree.Reorder.Proofs
