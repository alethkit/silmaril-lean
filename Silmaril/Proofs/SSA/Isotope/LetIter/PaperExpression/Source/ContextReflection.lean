module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ProductSplit.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.FreeTree
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Equations

/-! # Reflection by induction on the number of ambient product and sum nodes -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.Proofs

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection.Proofs

universe u w

section Measure

variable {α : Type u} {ε : Type w}

def nodes : Ty α → Nat
  | .product A B | .coprod A B => nodes A + nodes B + 1
  | _ => 0

def contextNodes (Γ : EffectCtx (Ty α) ε) : Nat :=
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

theorem product_decreases (i : Fin Γ.length) (hty : (Γ.get i).1 = .product A B) :
    contextNodes (ProductSplit.splitCtx Γ i A B) < contextNodes Γ := by
  have hw := contextNodes_set i A
  rw [hty, nodes] at hw
  change nodes B + contextNodes (SumSplit.branchCtx Γ i A) < contextNodes Γ
  omega

theorem sum_left_decreases (i : Fin Γ.length) (hty : (Γ.get i).1 = .coprod A B) :
    contextNodes (SumSplit.branchCtx Γ i A) < contextNodes Γ := by
  have hw := contextNodes_set i A
  rw [hty, nodes] at hw
  omega

theorem sum_right_decreases (i : Fin Γ.length) (hty : (Γ.get i).1 = .coprod A B) :
    contextNodes (SumSplit.branchCtx Γ i B) < contextNodes Γ := by
  have hw := contextNodes_set i B
  rw [hty, nodes] at hw
  omega

theorem inputTypes_branch (h : ∀ i : Fin Γ.length, InputType (Γ.get i).1)
    (i : Fin Γ.length) {X : Ty α} (hx : InputType X) :
    ∀ j : Fin (SumSplit.branchCtx Γ i X).length,
      InputType ((SumSplit.branchCtx Γ i X).get j).1 := by
  intro j
  let k : Fin Γ.length := j.cast List.length_set
  have hk : j = k.cast List.length_set.symm := Fin.ext rfl
  rw [hk]
  by_cases he : i.val = k.val
  · rw [← Fin.ext he]
    have hget : (SumSplit.branchCtx Γ i X).get (i.cast List.length_set.symm) = (X, ⊥) :=
      List.getElem_set_self _
    rw [hget]
    exact hx
  · have hget : (SumSplit.branchCtx Γ i X).get (k.cast List.length_set.symm) = Γ.get k :=
      List.getElem_set_ne he _
    rw [hget]
    exact h k

theorem inputTypes_product (h : ∀ i : Fin Γ.length, InputType (Γ.get i).1)
    (i : Fin Γ.length) (ha : InputType A) (hb : InputType B) :
    ∀ j : Fin (ProductSplit.splitCtx Γ i A B).length,
      InputType ((ProductSplit.splitCtx Γ i A B).get j).1 := by
  intro j
  exact Fin.cases (motive := fun k => InputType ((ProductSplit.splitCtx Γ i A B).get k).1) hb
    (inputTypes_branch h i ha) j

end Measure

variable {α Φ : Type u} (S : FreeTree.Signature α Φ)
  {ε : Type w} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  [DecidableEq α]

theorem reflect_aux (e : ε) {C : Ty α} (size : Nat) :
    letI := S.endpoints
    ∀ {Γ : EffectCtx (Ty α) ε} {a b : Expr Φ} {t s : Tm Empty Φ Γ.length},
      contextNodes Γ = size → Γ.Pure → (∀ i : Fin Γ.length, InputType (Γ.get i).1) →
      Wf Γ a C (⊥ : ε) → Wf Γ b C (⊥ : ε) →
      a.toLetIter Γ.length = some t → b.toLetIter Γ.length = some s →
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s C →
      Eqv Γ C e a b := by
  classical
  let instr := S.endpoints
  induction size using Nat.strong_induction_on with
  | ind size ih =>
    intro Γ a b t s hsize hΓ hInput ha hb ht hs hn
    by_cases hats : ∀ i : Fin Γ.length, ∃ x : α, (Γ.get i).1 = .base x
    · choose sorts hsorts using hats
      exact (FreeTree.Normalization.endpoint_reflection_atomic_inputs S hΓ hsorts e ha hb ht hs).mp hn
    · obtain ⟨i, hi⟩ := not_forall.mp hats
      have hshape := hInput i
      cases htype : (Γ.get i).1 with
      | base x => exact (hi ⟨x, htype⟩).elim
      | unit => rw [htype] at hshape; exact hshape.elim
      | empty => rw [htype] at hshape; exact hshape.elim
      | product A B =>
        rw [htype] at hshape
        have hdec : contextNodes (ProductSplit.splitCtx Γ i A B) < size :=
          hsize ▸ product_decreases i htype
        obtain ⟨_, _, ht', hs', hn'⟩ := ProductSplit.native_split i hΓ htype ht hs hn
        have he := ih _ hdec rfl (ProductSplit.splitCtx_pure hΓ i A B)
          (inputTypes_product hInput i hshape.1 hshape.2)
          (ProductSplit.wf_split i htype (hΓ i) ha) (ProductSplit.wf_split i htype (hΓ i) hb) ht' hs' hn'
        exact (ProductSplit.eqv_iff_split i htype (hΓ i)
          (wf_wkEff ha bot_le) (wf_wkEff hb bot_le)).mpr he
      | coprod A B =>
        rw [htype] at hshape
        have hdecL : contextNodes (SumSplit.branchCtx Γ i A) < size := hsize ▸ sum_left_decreases i htype
        have hdecR : contextNodes (SumSplit.branchCtx Γ i B) < size := hsize ▸ sum_right_decreases i htype
        obtain ⟨_, _, htL, hsL, hnL⟩ := SumSplit.TreeProofs.native_subst hΓ ht hs hn
          (SumSplit.Proofs.left_typed i htype (hΓ i))
        obtain ⟨_, _, htR, hsR, hnR⟩ := SumSplit.TreeProofs.native_subst hΓ ht hs hn
          (SumSplit.Proofs.right_typed i htype (hΓ i))
        obtain ⟨haL, haR⟩ := SumSplit.wf_specializations i htype (hΓ i) ha
        obtain ⟨hbL, hbR⟩ := SumSplit.wf_specializations i htype (hΓ i) hb
        have hL := ih _ hdecL rfl (SumSplit.branchCtx_pure hΓ i A)
          (inputTypes_branch hInput i hshape.1) haL hbL htL hsL hnL
        have hR := ih _ hdecR rfl (SumSplit.branchCtx_pure hΓ i B)
          (inputTypes_branch hInput i hshape.2) haR hbR htR hsR hnR
        exact (SumSplit.eqv_iff_specializations i htype (hΓ i)
          (wf_wkEff ha bot_le) (wf_wkEff hb bot_le)).mpr ⟨hL, hR⟩

public theorem endpoint_reflection_all_results {Γ : EffectCtx (Ty α) ε} {C : Ty α} {a b : Expr Φ}
    (hΓ : Γ.Pure) (hInput : ∀ i : Fin Γ.length, InputType (Γ.get i).1) (e : ε)
    (ha : letI := S.endpoints; Wf Γ a C (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ b C (⊥ : ε))
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s C ↔
      Eqv Γ C e a b := by
  let instr := S.endpoints
  exact ⟨reflect_aux S e (contextNodes Γ) rfl hΓ hInput ha hb ht hs, fun h => h.toLetIter ht hs⟩

end Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection.Proofs
