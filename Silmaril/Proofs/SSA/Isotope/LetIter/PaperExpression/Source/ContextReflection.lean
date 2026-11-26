module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ProductSplit.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.UnitSlot.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Packing.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

/-! # Reflection by induction on the number of ambient compound and nullary nodes -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection.Proofs

universe u v w

section Measure

variable {α : Type u} {ε : Type w}

def nodes : Ty α → Nat
  | .product A B | .coprod A B => nodes A + nodes B + 1
  | .unit | .empty => 1
  | .base _ => 0

public def contextNodes (Γ : EffectCtx (Ty α) ε) : Nat :=
  (Γ.map fun slot => nodes slot.1).sum

variable [Bot ε] {Γ : EffectCtx (Ty α) ε} {A B : Ty α}

theorem contextNodes_set (i : Fin Γ.length) (X : Ty α) :
    contextNodes (SumSplit.branchCtx Γ i X) + nodes (Γ.get i).1 =
      contextNodes Γ + nodes X := by
  induction Γ with
  | nil => exact i.elim0
  | cons slot Γ ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [contextNodes, Nat.add_comm, Nat.add_left_comm]
    · have h := ih j
      simp [contextNodes] at h ⊢
      omega

public theorem product_decreases (i : Fin Γ.length) (hty : (Γ.get i).1 = .product A B) :
    contextNodes (ProductSplit.splitCtx Γ i A B) < contextNodes Γ := by
  have hw := contextNodes_set i A
  rw [hty, nodes] at hw
  change nodes B + contextNodes (SumSplit.branchCtx Γ i A) < contextNodes Γ
  omega

public theorem sum_left_decreases (i : Fin Γ.length) (hty : (Γ.get i).1 = .coprod A B) :
    contextNodes (SumSplit.branchCtx Γ i A) < contextNodes Γ := by
  have hw := contextNodes_set i A
  rw [hty, nodes] at hw
  omega

public theorem sum_right_decreases (i : Fin Γ.length) (hty : (Γ.get i).1 = .coprod A B) :
    contextNodes (SumSplit.branchCtx Γ i B) < contextNodes Γ := by
  have hw := contextNodes_set i B
  rw [hty, nodes] at hw
  omega

omit [Bot ε] in
theorem contextNodes_erase (i : Fin Γ.length) :
    contextNodes (UnitSlot.eraseCtx Γ i) + nodes (Γ.get i).1 = contextNodes Γ := by
  induction Γ with
  | nil => exact i.elim0
  | cons slot Γ ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [contextNodes, Nat.add_comm]
    · have h := ih j
      simp [contextNodes, UnitSlot.eraseCtx] at h ⊢
      omega

omit [Bot ε] in
public theorem unit_decreases (i : Fin Γ.length) (hty : (Γ.get i).1 = .unit) :
    contextNodes (UnitSlot.eraseCtx Γ i) < contextNodes Γ := by
  have hw := contextNodes_erase i
  rw [hty, nodes] at hw
  omega

end Measure

section Cover

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]
  {ε : Type w} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

private theorem reflect_aux (lo e : ε) (hle : lo ≤ e) {C : Ty α} (size : Nat)
    (atomic : ∀ {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}
      {a b : Expr Φ} {t s : Tm Empty Φ Γ.length},
      Γ.Pure → (∀ i, (Γ.get i).1 = .base (slots i)) →
      Wf Γ a C lo → Wf Γ b C lo →
      a.toLetIter Γ.length = some t → b.toLetIter Γ.length = some s →
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s C →
      Eqv Γ C e a b) :
    ∀ {Γ : EffectCtx (Ty α) ε} {a b : Expr Φ} {t s : Tm Empty Φ Γ.length},
      contextNodes Γ = size → Γ.Pure →
      Wf Γ a C lo → Wf Γ b C lo →
      a.toLetIter Γ.length = some t → b.toLetIter Γ.length = some s →
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s C →
      Eqv Γ C e a b := by
  classical
  induction size using Nat.strong_induction_on with
  | ind size ih =>
    intro Γ a b t s hsize hΓ ha hb ht hs hn
    by_cases hats : ∀ i : Fin Γ.length, ∃ x : α, (Γ.get i).1 = .base x
    · choose sorts hsorts using hats
      exact atomic hΓ hsorts ha hb ht hs hn
    · obtain ⟨i, hi⟩ := not_forall.mp hats
      cases htype : (Γ.get i).1 with
      | base x => exact (hi ⟨x, htype⟩).elim
      | unit =>
        have hdec : contextNodes (UnitSlot.eraseCtx Γ i) < size := hsize ▸ unit_decreases i htype
        obtain ⟨_, _, ht', hs', hn'⟩ := UnitSlot.native_specializeUnit i hΓ htype ht hs hn
        have he := ih _ hdec rfl (UnitSlot.eraseCtx_pure hΓ i)
          (UnitSlot.wf_specializeUnit i htype (hΓ i) ha)
          (UnitSlot.wf_specializeUnit i htype (hΓ i) hb) ht' hs' hn'
        exact (UnitSlot.eqv_iff_specializeUnit i htype (hΓ i)
          (ha.weakenEffect hle) (hb.weakenEffect hle)).mpr he
      | empty =>
        exact eqv_of_empty_slot i htype (hΓ i) (ha.weakenEffect hle) (hb.weakenEffect hle)
      | product A B =>
        have hdec : contextNodes (ProductSplit.splitCtx Γ i A B) < size :=
          hsize ▸ product_decreases i htype
        obtain ⟨_, _, ht', hs', hn'⟩ := ProductSplit.native_split i hΓ htype ht hs hn
        have he := ih _ hdec rfl (ProductSplit.splitCtx_pure hΓ i A B)
          (ProductSplit.wf_split i htype (hΓ i) ha) (ProductSplit.wf_split i htype (hΓ i) hb) ht' hs' hn'
        exact (ProductSplit.eqv_iff_split i htype (hΓ i)
          (ha.weakenEffect hle) (hb.weakenEffect hle)).mpr he
      | coprod A B =>
        have hdecL : contextNodes (SumSplit.branchCtx Γ i A) < size := hsize ▸ sum_left_decreases i htype
        have hdecR : contextNodes (SumSplit.branchCtx Γ i B) < size := hsize ▸ sum_right_decreases i htype
        obtain ⟨⟨_, _, htL, hsL, hnL⟩, ⟨_, _, htR, hsR, hnR⟩⟩ :=
          SumSplit.native_specializations i hΓ htype ht hs hn
        obtain ⟨haL, haR⟩ := SumSplit.wf_specializations i htype (hΓ i) ha
        obtain ⟨hbL, hbR⟩ := SumSplit.wf_specializations i htype (hΓ i) hb
        have hL := ih _ hdecL rfl (SumSplit.branchCtx_pure hΓ i A)
          haL hbL htL hsL hnL
        have hR := ih _ hdecR rfl (SumSplit.branchCtx_pure hΓ i B)
          haR hbR htR hsR hnR
        exact (SumSplit.eqv_iff_specializations i htype (hΓ i)
          (ha.weakenEffect hle) (hb.weakenEffect hle)).mpr ⟨hL, hR⟩

/-- Transport reflection through the recursive cover by pure atomic contexts. -/
public theorem reflect_of_atomic (lo e : ε) (hle : lo ≤ e) {C : Ty α}
    (atomic : ∀ {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}
      {a b : Expr Φ} {t s : Tm Empty Φ Γ.length},
      Γ.Pure → (∀ i, (Γ.get i).1 = .base (slots i)) →
      Wf Γ a C lo → Wf Γ b C lo →
      a.toLetIter Γ.length = some t → b.toLetIter Γ.length = some s →
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s C →
      Eqv Γ C e a b)
    {Γ : EffectCtx (Ty α) ε} {a b : Expr Φ} {t s : Tm Empty Φ Γ.length}
    (hΓ : Γ.Pure) (ha : Wf Γ a C lo) (hb : Wf Γ b C lo)
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s)
    (hn : AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s C) :
    Eqv Γ C e a b :=
  reflect_aux lo e hle (contextNodes Γ) atomic rfl hΓ ha hb ht hs hn

end Cover

variable {α Φ : Type u} (S : FreeTree.Signature α Φ)
  {ε : Type w} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  [DecidableEq α]

public theorem endpoint_reflection_all_contexts {Γ : EffectCtx (Ty α) ε} {C : Ty α} {a b : Expr Φ}
    (hΓ : Γ.Pure) (e : ε)
    (ha : letI := S.endpoints; Wf Γ a C (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ b C (⊥ : ε))
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s C ↔
      Eqv Γ C e a b := by
  let instr := S.endpoints
  refine ⟨reflect_of_atomic ⊥ e bot_le ?_ hΓ ha hb ht hs, fun h => h.toLetIter ht hs⟩
  intro Δ slots a b t s hΔ hslots ha hb ht hs hn
  exact (FreeTree.Normalization.endpoint_reflection_atomic_inputs S hΔ hslots e ha hb ht hs).mp hn

end Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection.Proofs
