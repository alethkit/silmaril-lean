module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionProjection

/-! # Categorical selection of quantitative substitution entries -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F) (E : ControlEffects K) (N : ControlEnvironment K)

theorem split_tensor_discard_left {n : Nat} {Γ Γl Γr : QCtx τ n} {A : τ}
    (s : Γ.Split Γl Γr) (hd : Γl.Discardable) (f : M.Hom (packed Γr) A) :
    M.compose (split M.toSeqData s)
      (M.compose (M.tensor (discard M.toSeqData hd) f) (M.leftUnitor A)) =
      M.compose (weaken M.toSeqData (s.weakenRight hd)) f := by
  have he := congrArg (fun k => M.compose k f) (split_weakenRight M s hd)
  simpa only [discard, M.toSeqData.tensor_discard_left, M.toSeqData.compose_assoc] using he

theorem split_tensor_discard_right {n : Nat} {Γ Γl Γr : QCtx τ n} {A : τ}
    (s : Γ.Split Γl Γr) (hd : Γr.Discardable) (f : M.Hom (packed Γl) A) :
    M.compose (split M.toSeqData s)
      (M.compose (M.tensor f (discard M.toSeqData hd)) (M.rightUnitor A)) =
      M.compose (weaken M.toSeqData (s.weakenLeft hd)) f := by
  have he := congrArg (fun k => M.compose k f) (split_weakenLeft M s hd)
  simpa only [discard, M.toSeqData.tensor_discard_right, M.toSeqData.compose_assoc] using he

private theorem denote_term_cast {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t t' : Term Φ n} {A : τ} (h : HasType F Γ e t A) (he : t = t') :
    denote M.toSeqData K (he ▸ h) = denote M.toSeqData K h := by
  cases he
  rfl

include E N in
set_option backward.isDefEq.respectTransparency false in
/-- Selecting a used substitution entry eliminates the other entries using their
own deletion allowances, and produces a native typing witness of that entry. -/
theorem denoteSubstitution_lookup_exists (p : Polarity) {η : ε}
    {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n} {e : ε} {σ : Fin n → Term Φ m}
    (h : Substitution F Γ e σ Δ) (hh : h.EffectAllowed p η) :
    ∀ (i : Fin n) (hi : Δ.VarAllowed i),
      ∃ k : HasType F Γ e (σ i) (Δ i).1,
        p.orient M.le
          (M.compose (denoteSubstitution M.toSeqData K h) («variable» M.toSeqData i hi))
          (denote M.toSeqData K k) := by
  induction h with
  | nil hd => exact fun i => Fin.elim0 i
  | @zero m n Γ Δ e σ h a A ih =>
    intro i
    refine Fin.cases ?_ (fun i hi => ?_) i
    · intro hi
      have bad : (Usage.used Quantity.linear : Usage) ≤ Usage.zero := by
        simpa [QCtx.VarAllowed, QCtx.effective, Usage.effective_linear] using hi.1
      exact False.elim bad
    · exact ih hh i ⟨hi.1, fun j hj => hi.2 j.succ (fun h => hj (Fin.succ_injective _ h))⟩
  | @cons m n Γ Γl Γr Δ e el er σ a A q s h ha hq hc hl hr ih =>
    intro i
    refine Fin.cases ?_ (fun i hi => ?_) i
    · intro hi
      have hd : Δ.Discardable := fun j => hi.2 j.succ (Fin.succ_ne_zero j)
      have hΓl := h.discardable hd
      obtain ⟨k, hk⟩ := denote_rename_exists M K N ha id (s.weakenRight hΓl)
      have hk' : ∃ k : HasType F Γ er a A, denote M.toSeqData K k =
          M.compose (weaken M.toSeqData (s.weakenRight hΓl)) (denote M.toSeqData K ha) := by
        exact ⟨(show Tm.rename id a = a from Tm.rename_id a) ▸ k,
          (denote_term_cast M K k (Tm.rename_id a)).trans hk⟩
      obtain ⟨k, hk⟩ := hk'
      refine ⟨k.effectMono hr, ?_⟩
      have hkE : denote M.toSeqData K (k.effectMono hr) =
          M.compose (weaken M.toSeqData (s.weakenRight hΓl)) (denote M.toSeqData K ha) :=
        (Models.denote_effectMono (algebra M.toSeqData K) k hr).trans hk
      have he := M.toSeqData.orient_compose_left p
        (M.toSeqData.orient_compose_right p
          (M.toSeqData.orient_tensor p (denoteSubstitution_discard M K E p h hh.1 hd)
            (show p.orient M.le (denote M.toSeqData K ha) (denote M.toSeqData K ha) from
              by cases p <;> exact M.toSeqData.le_refl _)) (M.leftUnitor A)) (split M.toSeqData s)
      rw [split_tensor_discard_left M s hΓl, ← hkE] at he
      change p.orient M.le
        (M.compose (M.compose (split M.toSeqData s)
          (M.tensor (denoteSubstitution M.toSeqData K h) (denote M.toSeqData K ha)))
          (M.compose (M.right (discard M.toSeqData hd) A) (M.leftUnitor A))) _
      rw [M.toSeqData.compose_assoc, ← M.toSeqData.compose_assoc (M.tensor _ _),
        M.toSeqData.tensor_right_after _ _ _ (discard_pure M.toSeqData hd)]
      exact he
    · have hhead : Usage.zero ≤ Usage.effective (.used q) (quantity A) :=
        hi.2 0 (Ne.symm (Fin.succ_ne_zero i))
      have hqa : Quantity.affine ≤ q ⊓ quantity A := (Usage.zero_le_used _).mp hhead
      have hA : Quantity.affine ≤ quantity A := hqa.trans inf_le_right
      have hΓr : Γr.Discardable :=
        QCtx.discardable_iff_linearity.mpr ((hqa.trans inf_le_left).trans hq)
      have htail : Δ.VarAllowed i :=
        ⟨hi.1, fun j hj => hi.2 j.succ (fun h => hj (Fin.succ_injective _ h))⟩
      obtain ⟨k, hk⟩ := ih hh.1 i htail
      obtain ⟨k', heq⟩ := denote_rename_exists M K N k id (s.weakenLeft hΓr)
      have hk' : ∃ k' : HasType F Γ el (σ i) (Δ i).1, denote M.toSeqData K k' =
          M.compose (weaken M.toSeqData (s.weakenLeft hΓr)) (denote M.toSeqData K k) := by
        exact ⟨(show Tm.rename id (σ i) = σ i from Tm.rename_id (σ i)) ▸ k',
          (denote_term_cast M K k' (Tm.rename_id (σ i))).trans heq⟩
      obtain ⟨k', hk'⟩ := hk'
      refine ⟨k'.effectMono hl, ?_⟩
      have hkE : denote M.toSeqData K (k'.effectMono hl) =
          M.compose (weaken M.toSeqData (s.weakenLeft hΓr)) (denote M.toSeqData K k) :=
        (Models.denote_effectMono (algebra M.toSeqData K) k' hl).trans hk'
      have he := M.toSeqData.orient_compose_left p
        (M.toSeqData.orient_compose_right p
          (M.toSeqData.orient_tensor p hk
            (M.toSeqData.discard_naturality p (denote M.toSeqData K ha)
              (discardable_quantity hΓr) hA ((hqa.trans inf_le_left).trans hh.2.1)
              (denote_effect K E ha))) (M.rightUnitor (Δ i).1)) (split M.toSeqData s)
      have hproj := split_tensor_discard_right M s hΓr (denote M.toSeqData K k)
      change M.compose (split M.toSeqData s)
        (M.compose (M.tensor (denote M.toSeqData K k)
          (M.discard (packed Γr) (discardable_quantity hΓr))) (M.rightUnitor (Δ i).1)) = _ at hproj
      rw [hproj, ← hkE] at he
      change p.orient M.le
        (M.compose (M.compose (split M.toSeqData s)
          (M.tensor (denoteSubstitution M.toSeqData K h) (denote M.toSeqData K ha)))
          (M.compose (M.right («variable» M.toSeqData i htail) A)
            (M.compose (M.left (Δ i).1 (M.discard A hA)) (M.rightUnitor (Δ i).1)))) _
      simp only [M.toSeqData.compose_assoc]
      rw [← M.toSeqData.compose_assoc (M.tensor _ _),
        M.toSeqData.tensor_right_after _ _ _ (variable_pure M.toSeqData i htail)]
      rw [← M.toSeqData.compose_assoc (M.tensor _ _), M.toSeqData.tensor_left_after]
      exact he

end Silmaril.Isotope.Refinement.Models.Denotation
