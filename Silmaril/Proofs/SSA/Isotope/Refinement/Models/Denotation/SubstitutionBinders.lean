module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionRenaming

/-! # Semantically inert binder normalization for substitution -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F) (N : ControlEnvironment K)

theorem denote_syntax_cast {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t t' : Term Φ n} {A : τ} (h : HasType F Γ e t A) (he : t = t') :
    denote M.toSeqData K (he ▸ h) = denote M.toSeqData K h := by
  cases he
  rfl

include N in
/-- A normalized binder has an actual typing witness with unchanged interpretation. -/
theorem denote_normalizeBinder_exists {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t : Term Φ (n + 1)} {A B : τ} (h : HasType F (Γ.snoc A) e t B) :
    ∃ k : HasType F (Γ.snoc A (.used (quantity A))) e t B,
      denote M.toSeqData K k = denote M.toSeqData K h := by
  let w : QCtx.Weakening (Γ.snoc A (.used (quantity A))) (Γ.snoc A) id :=
    .ofPointwise (fun i => Fin.cases rfl (fun _ => rfl) i) (fun i => by
      cases i using Fin.cases with
      | zero => simp [QCtx.effective]
      | succ j => exact le_rfl)
  have hw : weaken M.toSeqData w = M.identity (product (packed Γ) A) := by
    change M.right (weaken M.toSeqData (QCtx.Weakening.refl Γ)) A = _
    rw [weaken_refl, M.toSeqData.right_identity]
  obtain ⟨k, hk⟩ := denote_rename_exists M K N h id w
  refine ⟨(show Tm.rename id t = t from Tm.rename_id t) ▸ k, ?_⟩
  have ht := (denote_syntax_cast M K k (Tm.rename_id t)).trans hk
  have hz : M.compose (weaken M.toSeqData w) (denote M.toSeqData K h) =
      denote M.toSeqData K h := by
    change M.compose (B := product (packed Γ) A) (weaken M.toSeqData w)
      (denote M.toSeqData K (Γ := Γ.snoc A) h) = _
    exact (congrArg (fun f : M.Hom (product (packed Γ) A) (product (packed Γ) A) =>
      M.compose f (denote M.toSeqData K h)) hw).trans (M.toSeqData.identity_compose _)
  exact ht.trans hz

include N in
/-- Normalizing both product binders leaves their categorical action unchanged. -/
theorem denote_normalizeBinders₂_exists {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t : Term Φ (n + 2)} {A B C : τ} (h : HasType F ((Γ.snoc A).snoc B) e t C) :
    ∃ k : HasType F ((Γ.snoc A (.used (quantity A))).snoc B (.used (quantity B))) e t C,
      denote M.toSeqData K k = denote M.toSeqData K h := by
  let w : QCtx.Weakening
      ((Γ.snoc A (.used (quantity A))).snoc B (.used (quantity B)))
      ((Γ.snoc A).snoc B) id :=
    .ofPointwise (fun i => Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i) (fun i => by
      cases i using Fin.cases with
      | zero => simp [QCtx.effective]
      | succ j =>
        cases j using Fin.cases with
        | zero =>
          change Usage.effective (.used ⊤) (quantity A) ≤
            Usage.effective (.used (quantity A)) (quantity A)
          simp
        | succ k => exact le_rfl)
  have hw : weaken M.toSeqData w = M.identity (product (product (packed Γ) A) B) := by
    change M.right (M.right (weaken M.toSeqData (QCtx.Weakening.refl Γ)) A) B = _
    rw [weaken_refl, M.toSeqData.right_identity, M.toSeqData.right_identity]
  obtain ⟨k, hk⟩ := denote_rename_exists M K N h id w
  refine ⟨(show Tm.rename id t = t from Tm.rename_id t) ▸ k, ?_⟩
  have ht := (denote_syntax_cast M K k (Tm.rename_id t)).trans hk
  have hz : M.compose (weaken M.toSeqData w) (denote M.toSeqData K h) =
      denote M.toSeqData K h :=
    (congrArg (fun f : M.Hom (product (product (packed Γ) A) B) (product (product (packed Γ) A) B) =>
      M.compose f (denote M.toSeqData K h)) hw).trans (M.toSeqData.identity_compose _)
  exact ht.trans hz

end Silmaril.Isotope.Refinement.Models.Denotation
