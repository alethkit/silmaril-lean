module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.WitnessCoherence
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SequentialEquations
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.TypingTransport
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Instantiation
public import Silmaril.Raw.SSA.Isotope.Refinement.TypingSupport
public import Silmaril.Raw.SSA.Isotope.Refinement.TheorySubstitution

/-! # Compressing quantitative contexts

Deleting a zero slot requires substitution stability, rather than just
weakening stability. Bundling retained slots uses the native product binder.
These transformations reduce contextual validity to singleton validity without
postulating semantic soundness of the primitive relation.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Isotope.Refinement
open LetIter.LocallyNameless
universe u v w r

namespace Term
variable {Φ : Type w}
/-- Substitution depends only on variables that occur in the term. -/
theorem bsubst_congr_support {n m : Nat} (t : Term Φ n)
    (σ θ : Fin n → Term Φ m) (h : ∀ i, uses t i = true → σ i = θ i) :
    Tm.bsubst σ t = Tm.bsubst θ t := by
  have up {n m : Nat} {σ θ : Fin n → Term Φ m} {p : Fin (n + 1) → Bool}
      (h : ∀ i, p i.succ = true → σ i = θ i) :
      ∀ i, p i = true → Tm.upSub σ i = Tm.upSub θ i := by
    intro i hi
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact congrArg Tm.lift (h i hi)
  induction t generalizing m with
  | bv i => exact h i (by simp [uses])
  | fv x => exact nomatch x
  | unit => rfl
  | op f a ih => exact congrArg (Tm.op f) (ih σ θ h)
  | pair a b iha ihb =>
    exact congrArg₂ Tm.pair (iha σ θ (fun i hi => h i (by simp [uses, hi])))
      (ihb σ θ (fun i hi => h i (by simp [uses, hi])))
  | let₁ a b iha ihb =>
    exact congrArg₂ Tm.let₁ (iha σ θ (fun i hi => h i (by simp [uses, hi])))
      (ihb _ _ (up (fun i hi => h i (by simp [uses, hi]))))
  | let₂ a b iha ihb =>
    exact congrArg₂ Tm.let₂ (iha σ θ (fun i hi => h i (by simp [uses, hi])))
      (ihb _ _ (up (up (fun i hi => h i (by simp [uses, hi])))))
  | inl a ih => exact congrArg Tm.inl (ih σ θ h)
  | inr a ih => exact congrArg Tm.inr (ih σ θ h)
  | abort a ih => exact congrArg Tm.abort (ih σ θ h)
  | case a l r iha ihl ihr =>
    have ha := iha σ θ (fun i hi => h i (by simp [uses, hi]))
    have hl := ihl _ _ (up (fun i hi => h i (by simp [uses, hi])))
    have hr := ihr _ _ (up (fun i hi => h i (by simp [uses, hi])))
    simp only [Tm.bsubst, ha, hl, hr]
  | iter a b iha ihb =>
    exact congrArg₂ Tm.iter (iha σ θ (fun i hi => h i (by simp [uses, hi])))
      (ihb _ _ (up (fun i hi => h i (by simp [uses, hi]))))
end Term

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment}

namespace Substitution.Admissible
/-- The omitted entry can be replaced by arbitrary raw syntax. -/
theorem dropZero {n : Nat} (Γ : QCtx τ n) (A : τ) (a : Term Φ n) :
    Admissible F Γ (⊥ : ε) (Fin.cases a Tm.bv) (Γ.snoc A .zero) := by
  obtain ⟨Θ, w, ⟨h⟩⟩ := id (F := F) (Φ := Φ) Γ (⊥ : ε)
  refine ⟨Θ.snoc A .zero, ?_, ⟨.zero h a A⟩⟩
  convert w.up A .zero using 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i
end Substitution.Admissible

namespace HasType
/-- Re-inserting an omitted slot after deleting it leaves formed syntax unchanged. -/
theorem rename_dropZeroUnder {n : Nat} {Γ : QCtx τ n} {A B C : τ} {e : ε}
    {t : Term Φ (n + 2)} (h : HasType F ((Γ.snoc A .zero).snoc B) e t C) :
    Tm.rename (Tm.up Fin.succ)
      (Tm.bsubst (Tm.upSub (Fin.cases (.unit : Term Φ n) Tm.bv)) t) = t := by
  rw [Tm.rename_bsubst]
  trans Tm.bsubst Tm.bv t
  · apply Term.bsubst_congr_support
    intro i hi
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      cases i using Fin.cases with
      | zero => exact False.elim (h.used_nonzero hi rfl)
      | succ i => rfl
  · exact Tm.bsubst_id t
end HasType

namespace HasType
/-- Bundle the two most recent default binders into a single product input. -/
def bundleLast {n : Nat} {Γ : QCtx τ n} {A B C : τ} {e : ε}
    {t : Term Φ (n + 2)} (h : HasType F ((Γ.snoc A).snoc B) e t C) :
    HasType F (Γ.snoc (product A B)) e (.let₂ (.bv 0) t.underTwoBinders) C :=
  .let₂ ((QCtx.Split.zero_right Γ).snoc (.right (.used ⊤)))
    (.var 0 (QCtx.varAllowed_snoc (QCtx.zero_discardable Γ) (product A B)))
    (h.rename _ (QCtx.Weakening.insertZeroUnderTwo Γ (product A B) A B))
end HasType

/-- Product abstraction is a native congruence, with only weakening used on its body. -/
theorem Refines.bundleLast {R : Relation τ Φ} (hR : R.RenamingClosed)
    {n : Nat} {Γ : QCtx τ n} {A B C : τ} {a b : Term Φ (n + 2)}
    (h : Refines (ε := ε) F R ((Γ.snoc A).snoc B) a b C) :
    Refines (ε := ε) F R (Γ.snoc (product A B))
      (.let₂ (.bv 0) a.underTwoBinders) (.let₂ (.bv 0) b.underTwoBinders) C :=
  .let₂ ((QCtx.Split.zero_right Γ).snoc (.right (.used ⊤)))
    (.refl ⟨.var 0 (QCtx.varAllowed_snoc (QCtx.zero_discardable Γ) (product A B))⟩)
    (h.rename _ (QCtx.Weakening.insertZeroUnderTwo Γ (product A B) A B) hR)

namespace QCtx.Weakening
/-- Intrinsic type quantity permits replacing a retained annotation by the default. -/
theorem saturateUnder {n : Nat} (Γ : QCtx τ n) (A B : τ) (q : Quantity) :
    Weakening ((Γ.snoc A).snoc B) ((Γ.snoc A (.used q)).snoc B) id := by
  have hq : Usage.effective (.used q) (quantity A) ≤
      Usage.effective (.used ⊤) (quantity A) := by
    change q ⊓ quantity A ≤ ⊤ ⊓ quantity A
    exact inf_le_inf le_top le_rfl
  convert (cons (refl Γ) hq).up B using 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
end QCtx.Weakening

namespace Models.Denotation
variable (M : SeqModel.{u,v,w,r} τ Φ ε) (K : ControlData M.toSeqData F)
variable (N : ControlEnvironment K) (H : WitnessCoherent M K)

/-- Term-equality transport leaves the interpreted arrow unchanged. -/
theorem denote_term_cast {n : Nat} {Γ : QCtx τ n} {e : ε} {t t' : Term Φ n} {A : τ}
    (h : HasType F Γ e t A) (ht : t = t') :
    denote M.toSeqData K (ht ▸ h) = denote M.toSeqData K h := by
  cases ht
  rfl

include N H in
/-- Zero-slot deletion is semantically invisible, including under a retained binder. -/
theorem denote_dropZeroUnder {n : Nat} {Γ : QCtx τ n} {A B C : τ} {e e' : ε}
    {t : Term Φ (n + 2)} (h : HasType F ((Γ.snoc A .zero).snoc B) e t C)
    (k : HasType F (Γ.snoc B) e'
      (Tm.bsubst (Tm.upSub (Fin.cases (.unit : Term Φ n) Tm.bv)) t) C) :
    denote M.toSeqData K h = denote M.toSeqData K k := by
  let w := (QCtx.Weakening.insertZero Γ A).up B
  have hr := h.rename_dropZeroUnder
  let k' : HasType F ((Γ.snoc A .zero).snoc B) e _ C := hr.symm ▸ h
  have he := denote_rename_of_typing M K N H k (Tm.up Fin.succ) w k'
  have he' : denote M.toSeqData K k' = denote M.toSeqData K h := by
    exact denote_term_cast M K h hr.symm
  rw [he'] at he
  change denote M.toSeqData K h =
    M.compose (M.right (weaken M.toSeqData (QCtx.Weakening.insertZero Γ A)) B)
      (denote M.toSeqData K k) at he
  have hz : weaken M.toSeqData (QCtx.Weakening.insertZero Γ A) = M.identity (packed Γ) := by
    exact (congrArg Subtype.val (weakenPure_skip M (QCtx.Weakening.refl Γ)
      (A := A) (q := .zero) le_rfl)).trans (weaken_refl M.toSeqData Γ)
  rw [hz] at he
  exact he.trans ((congrArg (fun f => M.compose f (denote M.toSeqData K k))
    (M.toSeqData.right_identity (packed Γ) B)).trans (M.toSeqData.identity_compose _))


include N H in
/-- Restricting only a retained variable's annotation does not alter interpretation. -/
theorem denote_saturateUnder {n : Nat} {Γ : QCtx τ n} {A B C : τ} {q : Quantity}
    {e e' : ε} {t : Term Φ (n + 2)}
    (h : HasType F ((Γ.snoc A (.used q)).snoc B) e t C)
    (k : HasType F ((Γ.snoc A).snoc B) e' t C) :
    denote M.toSeqData K h = denote M.toSeqData K k := by
  let w := QCtx.Weakening.saturateUnder Γ A B q
  let k' : HasType F ((Γ.snoc A).snoc B) e' (Tm.rename id t) C := (Tm.rename_id t).symm ▸ k
  have he := denote_rename_of_typing M K N H h id w k'
  rw [denote_term_cast M K k (Tm.rename_id t).symm] at he
  have hw : weaken M.toSeqData w = M.identity (product (product (packed Γ) A) B) := by
    change M.right (M.right (weaken M.toSeqData (QCtx.Weakening.refl Γ)) A) B = _
    rw [weaken_refl, M.toSeqData.right_identity, M.toSeqData.right_identity]
  rw [hw] at he
  exact (he.trans (M.toSeqData.identity_compose _)).symm

set_option backward.isDefEq.respectTransparency false in
include N H in
/-- Native product abstraction acts by the structural reassociation isomorphism. -/
theorem denote_bundleLast {n : Nat} {Γ : QCtx τ n} {A B C : τ} {e : ε}
    {t : Term Φ (n + 2)} (h : HasType F ((Γ.snoc A).snoc B) e t C) :
    denote M.toSeqData K h.bundleLast =
      M.compose (M.associatorInv (packed Γ) A B) (denote M.toSeqData K h) := by
  let hv : HasType F (Γ.zero.snoc (product A B)) e (.bv 0 : Term Φ (n + 1)) (product A B) :=
    .var 0 (QCtx.varAllowed_snoc (QCtx.zero_discardable Γ) (product A B))
  let kc := h.rename _ (QCtx.Weakening.insertZeroUnderTwo Γ (product A B) A B)
  let si := (QCtx.Split.zero_right Γ).snoc (.right (.used ⊤)) (A := product A B)
  change M.compose (split M.toSeqData si)
    (M.compose (M.left (packed Γ) (denote M.toSeqData K hv))
      (M.compose (M.associatorInv (packed Γ) A B) (denote M.toSeqData K kc))) = _
  rw [Sequential.denote_underTwoBinders_zero M K N H h kc]
  rw [← M.toSeqData.compose_assoc]
  change M.compose
    (M.compose (split M.toSeqData si) (M.left (packed Γ)
      (M.compose (M.right (discard M.toSeqData (QCtx.zero_discardable Γ)) (product A B))
        (M.leftUnitor (product A B)))))
    (M.compose (M.associatorInv (packed Γ) A B) (denote M.toSeqData K h)) = _
  rw [newest_split_variable M Γ (product A B) (QCtx.zero_discardable Γ)]
  exact M.toSeqData.identity_compose _

end Models.Denotation
end Silmaril.Isotope.Refinement
