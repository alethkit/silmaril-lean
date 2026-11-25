module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ControlSubstitution
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.BetaContexts
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionInstantiation
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionIdentity

/-! # Actual directed beta soundness for all control fragments -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F) (E : ControlEffects K)
variable (N : ControlEnvironment K) (H : WitnessCoherent M K)
namespace Sequential
include E N H

set_option backward.isDefEq.respectTransparency false in
/-- Quantitative beta constructs a native substituted endpoint and compares its
interpretation with execution of the initializer followed by the body. -/
theorem denote_beta_exists (p : Polarity)
    (S : ∀ {n : Nat} (t : Term Φ n), SubstitutionSoundAt M K p t) {n : Nat} {Γ Γl Γr : QCtx τ n}
    {e η : ε} {a : Term Φ n} {b : Term Φ (n + 1)} {A B : τ} {q : Usage}
    (s : Γ.Split Γl Γr) (ha : HasType F Γl e a A)
    (hb : HasType F (Γr.snoc A q) η b B)
    (hd : HasType F (Γr.snoc A) η b B)
    (hm : EffectSystem.moves p e η)
    (hq : q ≤ Usage.used (Γl.linearity ⊓ EffectSystem.quantity p e)) :
    ∃ k : HasType F Γ (e ⊔ η) (Tm.instantiate b a) B,
      p.orient M.le
        (M.compose (split M.toSeqData s.symm)
          (M.compose (M.left (packed Γr) (denote M.toSeqData K ha)) (denote M.toSeqData K hd)))
        (denote M.toSeqData K k) := by
  obtain ⟨Θ, w, hi, hig, hie⟩ := denoteSubstitution_identity_exists M
    K N p η Γr
  have wb : QCtx.Weakening (Θ.snoc A q) (Γr.snoc A q) id := by
    convert QCtx.Weakening.cons w (A := A) (q := q) (q' := q) le_rfl using 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  obtain ⟨hbr, hbre⟩ := denote_rename_exists M K N hb id wb
  let hbn : HasType F (Θ.snoc A q) η b B := (Tm.rename_id b) ▸ hbr
  have hbne : denote M.toSeqData K hbn = M.compose (weaken M.toSeqData wb) (denote M.toSeqData K hb) :=
    (denote_syntax_cast M K hbr (Tm.rename_id b)).trans hbre
  cases q with
  | used q =>
    have hqu : q ≤ Γl.linearity ⊓ EffectSystem.quantity p e := hq
    let hs : Substitution F Γ e (Fin.cases a Tm.bv) (Θ.snoc A (.used q)) :=
      .cons s.symm hi ha (hqu.trans inf_le_left) (EffectSystem.pure_commutes e) bot_le le_rfl
    have hsg : hs.EffectAllowed p η := ⟨hig, hqu.trans inf_le_right, hm⟩
    obtain ⟨k, hk⟩ := S b hbn hs hsg hm
    refine ⟨k, ?_⟩
    have he : M.compose (denoteSubstitution M.toSeqData K hs) (denote M.toSeqData K hbn) =
        M.compose (split M.toSeqData s.symm)
          (M.compose (M.left (packed Γr) (denote M.toSeqData K ha)) (denote M.toSeqData K hd)) := by
      rw [hbne]
      change M.compose
        (M.compose (split M.toSeqData s.symm)
          (M.tensor (denoteSubstitution M.toSeqData K hi) (denote M.toSeqData K ha)))
        (M.compose (M.right (weaken M.toSeqData w) A) (denote M.toSeqData K hb)) = _
      rw [M.toSeqData.compose_assoc, ← M.toSeqData.compose_assoc
        (M.tensor (denoteSubstitution M.toSeqData K hi) (denote M.toSeqData K ha)),
        M.toSeqData.tensor_retract_left _ _ (weaken_pure _ w) hie,
        denote_binder_used M K N H hb hd]
    exact (congrArg (fun f => p.orient M.le f (denote M.toSeqData K k)) he).mp hk
  | zero =>
    have hqu : Quantity.affine ≤ Γl.linearity ⊓ EffectSystem.quantity p e :=
      (Usage.zero_le_used _).mp hq
    have hl : Γl.Discardable := QCtx.discardable_iff_linearity.mpr (hqu.trans inf_le_left)
    let wz := s.symm.weakenLeft hl
    obtain ⟨ht, htg, hte⟩ := denoteSubstitution_rename_exists M K
      N p hi hig id wz
    have hv : (fun i => Tm.rename id (Tm.bv i : Term Φ n)) = Tm.bv := rfl
    let ht' := hv ▸ ht
    have ht'g : ht'.EffectAllowed p η := (substitution_function_cast M K ht hv p η).2.mpr htg
    have ht'e : denoteSubstitution M.toSeqData K ht' =
        M.compose (weaken M.toSeqData wz) (denoteSubstitution M.toSeqData K hi) :=
      (substitution_function_cast M K ht hv p η).1.trans hte
    let hs : Substitution F Γ e (Fin.cases a Tm.bv) (Θ.snoc A .zero) :=
      (Substitution.zero ht' a A).effectMono bot_le
    have hzg : (Substitution.zero ht' a A).EffectAllowed p η := ht'g
    have hsg : hs.EffectAllowed p η := hzg.effectMono bot_le
    obtain ⟨k, hk⟩ := S b hbn hs hsg hm
    refine ⟨k, ?_⟩
    have hse : denoteSubstitution M.toSeqData K hs =
        M.compose (weaken M.toSeqData wz) (denoteSubstitution M.toSeqData K hi) :=
      (denoteSubstitution_effectMono M.toSeqData K (.zero ht' a A) bot_le).trans ht'e
    have he : M.compose (denoteSubstitution M.toSeqData K hs) (denote M.toSeqData K hbn) =
        M.compose (weaken M.toSeqData wz) (denote M.toSeqData K (Γ := Γr.snoc A .zero) hb) := by
      rw [hse, hbne]
      exact M.toSeqData.substitution_retract _ _ _ hie _
    replace hk := (congrArg (fun f => p.orient M.le f (denote M.toSeqData K k)) he).mp hk
    have hA := zero_binder_affine hb hd
    have hdel := split_delete_right M p s.symm (denote M.toSeqData K ha)
      (denote M.toSeqData K (Γ := Γr.snoc A .zero) hb) hl hA (hqu.trans inf_le_right) (denote_effect K E ha)
    have hde := denote_binder_zero M K N H hb hd hA
    rw [← hde] at hdel
    exact M.toSeqData.orient_trans p hdel hk

/-- The written beta rule is sound for arbitrary typing witnesses of its endpoints. -/
theorem denote_beta (p : Polarity)
    (S : ∀ {n : Nat} (t : Term Φ n), SubstitutionSoundAt M K p t) {n : Nat} {Γ Γl Γr : QCtx τ n}
    {e η eL eR : ε} {a : Term Φ n} {b : Term Φ (n + 1)} {A B : τ} {q : Usage}
    (s : Γ.Split Γl Γr) (ha : HasType F Γl e a A)
    (hb : HasType F (Γr.snoc A q) η b B)
    (hd : HasType F (Γr.snoc A) η b B)
    (hm : EffectSystem.moves p e η)
    (hq : q ≤ Usage.used (Γl.linearity ⊓ EffectSystem.quantity p e))
    (hl : HasType F Γ eL (.let₁ a b) B)
    (hr : HasType F Γ eR (Tm.instantiate b a) B) :
    p.orient M.le (denote M.toSeqData K hl) (denote M.toSeqData K hr) := by
  obtain ⟨k, hk⟩ := denote_beta_exists M K E N H p S s ha hb hd hm hq
  let hleft : HasType F Γ (e ⊔ η) (.let₁ a b) B :=
    .let₁ s.symm (ha.effectMono le_sup_left) (hd.effectMono le_sup_right)
  have hel : denote M.toSeqData K hleft =
      M.compose (split M.toSeqData s.symm)
        (M.compose (M.left (packed Γr) (denote M.toSeqData K ha)) (denote M.toSeqData K hd)) := by
    exact congrArg₂ (fun (f : M.Hom (packed Γl) A) (g : M.Hom (product (packed Γr) A) B) =>
      M.compose (split M.toSeqData s.symm) (M.compose (M.left (packed Γr) f) g))
      (Models.denote_effectMono (algebra M.toSeqData K) ha le_sup_left)
      (Models.denote_effectMono (algebra M.toSeqData K) hd le_sup_right)
  have he := (H hl hleft).trans hel
  exact (congrArg₂ (fun f g => p.orient M.le f g) he (H hr k)).mpr hk

end Sequential
end Silmaril.Isotope.Refinement.Models.Denotation
