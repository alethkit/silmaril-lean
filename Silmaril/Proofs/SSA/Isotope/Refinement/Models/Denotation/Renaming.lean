module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.Restriction
public import Silmaril.Raw.SSA.Isotope.Refinement.Weakening

/-! # A semantically compatible native weakening derivation

This is an existence theorem for an actual typing witness. It does not assume
that an arbitrary chosen witness for the native weakening theorem has the same
denotation; that stronger conclusion requires typing coherence.
-/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F)

theorem denote_result_transport {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A B : τ}
    (h : HasType F Γ e t A) (he : A = B) :
    HEq (denote M.toSeqData K (he ▸ h)) (denote M.toSeqData K h) := by
  cases he
  rfl

theorem PureHom.val_heq {A B C D : τ} (hAB : A = B) (hCD : C = D)
    {f : PureHom M.toSeqData A C} {g : PureHom M.toSeqData B D} (h : HEq f g) : HEq f.val g.val := by
  cases hAB
  cases hCD
  exact heq_of_eq (congrArg Subtype.val (eq_of_heq h))

set_option backward.isDefEq.respectTransparency false in
/-- Every native context weakening has a typing witness commuting with interpretation. -/
theorem denote_rename_exists (N : ControlEnvironment K) {n : Nat} {Δ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (h : HasType F Δ e t A) :
    ∀ {m : Nat} {Γ : QCtx τ m} (ρ : Fin n → Fin m) (w : QCtx.Weakening Γ Δ ρ),
      ∃ h' : HasType F Γ e (Tm.rename ρ t) A,
        denote M.toSeqData K h' = M.toSeqData.compose (weaken M.toSeqData w) (denote M.toSeqData K h) := by
  induction h with
  | @var n Δ e i hi =>
    intro m Γ ρ w
    let hvar := HasType.var (Φ := Φ) (F := F) (e := e) (ρ i) (w.varAllowed hi)
    refine ⟨(w.types i) ▸ hvar, ?_⟩
    apply eq_of_heq
    exact (denote_result_transport M K hvar (w.types i)).trans
      (PureHom.val_heq M rfl (w.types i).symm (weakenPure_variable M w i hi)).symm
  | op hf ha ih =>
    intro m Γ ρ w
    obtain ⟨h', he⟩ := ih ρ w
    refine ⟨.op hf h', ?_⟩
    change M.toSeqData.compose (denote M.toSeqData K h') _ = _
    rw [he]
    exact M.toSeqData.compose_assoc _ _ _
  | unit hd =>
    intro m Γ ρ w
    refine ⟨.unit (w.discardable hd), ?_⟩
    exact (M.toSeqData.pure_discard_natural _ (weaken_pure _ _) _ _).symm
  | pair s ha hb iha ihb =>
    intro m Γ ρ w
    obtain ⟨Γl, Γr, ss, wl, wr, _⟩ := w.split s
    obtain ⟨ha', hea⟩ := iha ρ wl
    obtain ⟨hb', heb⟩ := ihb ρ wr
    refine ⟨.pair ss ha' hb', ?_⟩
    change M.toSeqData.compose (split M.toSeqData ss)
      (M.toSeqData.tensor (denote M.toSeqData K ha') (denote M.toSeqData K hb')) = _
    rw [hea, heb, ← M.toSeqData.tensor_comp_pure _ _ _ _ (weaken_pure _ wr),
      ← M.toSeqData.compose_assoc, ← weaken_split M w ss s wl wr]
    exact M.toSeqData.compose_assoc _ _ _
  | @let₁ n Δ Δl Δr e a b A B s ha hb iha ihb =>
    intro m Γ ρ w
    obtain ⟨Γl, Γr, ss, wl, wr, _⟩ := w.split s
    obtain ⟨ha', hea⟩ := iha ρ wr
    obtain ⟨hb', heb⟩ := ihb (Tm.up ρ) (.cons wl le_rfl)
    refine ⟨.let₁ ss ha' hb', ?_⟩
    change M.toSeqData.compose (split M.toSeqData ss)
      (M.toSeqData.compose (M.toSeqData.left _ (denote M.toSeqData K ha'))
        (denote M.toSeqData K hb')) = _
    rw [hea, heb]
    change M.toSeqData.compose (split M.toSeqData ss)
      (M.toSeqData.compose (M.toSeqData.left _ (M.toSeqData.compose (weaken M.toSeqData wr) (denote M.toSeqData K ha)))
        (M.toSeqData.compose (M.toSeqData.right (weaken M.toSeqData wl) A) (denote M.toSeqData K hb))) = _
    rw [← M.toSeqData.compose_assoc (M.toSeqData.left _ _) (M.toSeqData.right _ _),
      ← M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ wl)]
    simp only [← M.toSeqData.compose_assoc]
    rw [← weaken_split M w ss s wl wr]
    simp only [M.toSeqData.compose_assoc]
    rfl
  | @let₂ n Δ Δl Δr e a b A B C s ha hb iha ihb =>
    intro m Γ ρ w
    obtain ⟨Γl, Γr, ss, wl, wr, _⟩ := w.split s
    obtain ⟨ha', hea⟩ := iha ρ wr
    obtain ⟨hb', heb⟩ := ihb (Tm.up (Tm.up ρ)) (.cons (.cons wl le_rfl) le_rfl)
    refine ⟨.let₂ ss ha' hb', ?_⟩
    change M.toSeqData.compose (split M.toSeqData ss)
      (M.toSeqData.compose (M.toSeqData.left _ (denote M.toSeqData K ha'))
        (M.toSeqData.compose (M.toSeqData.associatorInv _ A B) (denote M.toSeqData K hb'))) = _
    rw [hea, heb]
    change M.toSeqData.compose (split M.toSeqData ss)
      (M.toSeqData.compose (M.toSeqData.left _ (M.toSeqData.compose (weaken M.toSeqData wr) (denote M.toSeqData K ha)))
        (M.toSeqData.compose (M.toSeqData.associatorInv _ A B)
          (M.toSeqData.compose (M.toSeqData.right (M.toSeqData.right (weaken M.toSeqData wl) A) B)
            (denote M.toSeqData K hb)))) = _
    rw [← M.toSeqData.compose_assoc (M.toSeqData.associatorInv _ A B),
      ← M.toSeqData.associatorInv_natural_left (weaken M.toSeqData wl)]
    simp only [M.toSeqData.compose_assoc]
    rw [← M.toSeqData.compose_assoc (M.toSeqData.left _ _) (M.toSeqData.right _ _),
      ← M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ wl)]
    simp only [← M.toSeqData.compose_assoc]
    rw [← weaken_split M w ss s wl wr]
    simp only [M.toSeqData.compose_assoc]
    rfl
  | inl hg ha ih =>
    intro m Γ ρ w
    obtain ⟨h', he⟩ := ih ρ w
    refine ⟨.inl hg h', ?_⟩
    change M.toSeqData.compose (denote M.toSeqData K h') _ = _
    rw [he]
    exact M.toSeqData.compose_assoc _ _ _
  | inr hg ha ih =>
    intro m Γ ρ w
    obtain ⟨h', he⟩ := ih ρ w
    refine ⟨.inr hg h', ?_⟩
    change M.toSeqData.compose (denote M.toSeqData K h') _ = _
    rw [he]
    exact M.toSeqData.compose_assoc _ _ _
  | abort hg ha ih =>
    intro m Γ ρ w
    obtain ⟨h', he⟩ := ih ρ w
    refine ⟨.abort hg h', ?_⟩
    change M.toSeqData.compose (denote M.toSeqData K h') _ = _
    rw [he]
    exact M.toSeqData.compose_assoc _ _ _
  | @case n Δ Δl Δr e a l r A B C hg s ha hl hr iha ihl ihr =>
    intro m Γ ρ w
    obtain ⟨Γl, Γr, ss, wl, wr, _⟩ := w.split s
    obtain ⟨ha', hea⟩ := iha ρ wr
    obtain ⟨hl', hel⟩ := ihl (Tm.up ρ) (.cons wl le_rfl)
    obtain ⟨hr', her⟩ := ihr (Tm.up ρ) (.cons wl le_rfl)
    refine ⟨.case hg ss ha' hl' hr', ?_⟩
    change M.toSeqData.compose (split M.toSeqData ss)
      (M.toSeqData.compose (M.toSeqData.left _ (denote M.toSeqData K ha'))
        (M.toSeqData.compose (K.distribute hg _ A B)
          (K.desc hg (denote M.toSeqData K hl') (denote M.toSeqData K hr')))) = _
    rw [hea, hel, her]
    change M.toSeqData.compose (split M.toSeqData ss)
      (M.toSeqData.compose (M.toSeqData.left _ (M.toSeqData.compose (weaken M.toSeqData wr) (denote M.toSeqData K ha)))
        (M.toSeqData.compose (K.distribute hg _ A B)
          (K.desc hg (M.toSeqData.compose (M.toSeqData.right (weaken M.toSeqData wl) A) (denote M.toSeqData K hl))
            (M.toSeqData.compose (M.toSeqData.right (weaken M.toSeqData wl) B) (denote M.toSeqData K hr))))) = _
    rw [← N.case_natural, ← M.toSeqData.compose_assoc (M.toSeqData.left _ _) (M.toSeqData.right _ _),
      ← M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ wl)]
    simp only [← M.toSeqData.compose_assoc]
    rw [← weaken_split M w ss s wl wr]
    simp only [M.toSeqData.compose_assoc]
    rfl
  | @iter n Δ Δl Δr e a b A B hg s hu hi ha hb iha ihb =>
    intro m Γ ρ w
    obtain ⟨Γl, Γr, ss, wl, wr, htop⟩ := w.split s
    obtain ⟨ha', hea⟩ := iha ρ wr
    obtain ⟨hb', heb⟩ := ihb (Tm.up ρ) (.cons wl le_rfl)
    refine ⟨.iter hg ss (htop hu) hi ha' hb', ?_⟩
    have hD : (⊤ : Quantity) ≤ quantity (packed Γl) := (htop hu) ▸ packed_quantity Γl
    have hE : (⊤ : Quantity) ≤ quantity (packed Δl) := hu ▸ packed_quantity Δl
    change M.toSeqData.compose (split M.toSeqData ss)
      (M.toSeqData.compose (M.toSeqData.left _ (denote M.toSeqData K ha'))
        (K.iterateWithContext hg _ (le_trans le_top hD) (le_trans le_top hD) (denote M.toSeqData K hb'))) = _
    rw [hea, heb]
    change M.toSeqData.compose (split M.toSeqData ss)
      (M.toSeqData.compose (M.toSeqData.left _ (M.toSeqData.compose (weaken M.toSeqData wr) (denote M.toSeqData K ha)))
        (K.iterateWithContext hg _ (le_trans le_top hD) (le_trans le_top hD)
          (M.toSeqData.compose (M.toSeqData.right (weaken M.toSeqData wl) A) (denote M.toSeqData K hb)))) = _
    rw [← N.iter_natural hg _ (weaken_pure _ wl) _ _ (le_trans le_top hE) (le_trans le_top hE),
      ← M.toSeqData.compose_assoc (M.toSeqData.left _ _) (M.toSeqData.right _ _),
      ← M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ wl)]
    simp only [← M.toSeqData.compose_assoc]
    rw [← weaken_split M w ss s wl wr]
    simp only [M.toSeqData.compose_assoc]
    rfl

end Silmaril.Isotope.Refinement.Models.Denotation
