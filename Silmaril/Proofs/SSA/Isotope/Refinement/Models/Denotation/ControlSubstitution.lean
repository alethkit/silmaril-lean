module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionLookup
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionSplitting
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionBinders
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionEvaluation

/-! # Directed substitution soundness through optional control -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F)

/-- Substitution soundness at one raw term, including every quantitative typing witness. -/
def SubstitutionSoundAt (p : Polarity) {n : Nat} (t : Term Φ n) : Prop :=
  ∀ {Δ : QCtx τ n} {η : ε} {A : τ} (ht : HasType F Δ η t A)
    {m : Nat} {Γ : QCtx τ m} {e : ε} {σ : Fin n → Term Φ m}
    (hs : Substitution F Γ e σ Δ) (_hh : hs.EffectAllowed p η)
    (_hm : EffectSystem.moves p e η),
    ∃ k : HasType F Γ (e ⊔ η) (Tm.bsubst σ t) A,
      p.orient M.le
        (M.compose (denoteSubstitution M.toSeqData K hs) (denote M.toSeqData K ht))
        (denote M.toSeqData K k)

variable (E : ControlEffects K) (N : ControlEnvironment K) (O : ControlMonotone K)

include E N O in
set_option backward.isDefEq.respectTransparency false in
/-- All non-loop constructors preserve directed quantitative substitution.
The separate loop step can be discharged with the categorical iteration laws. -/
theorem denote_bsubst_of_iteration (p : Polarity)
    (loop : ∀ {n : Nat} (a : Term Φ n) (b : Term Φ (n + 1)),
      SubstitutionSoundAt M K p a → SubstitutionSoundAt M K p b →
        SubstitutionSoundAt M K p (.iter a b))
    {n : Nat} (t : Term Φ n) : SubstitutionSoundAt M K p t := by
  induction t with
  | fv x => exact nomatch x
  | bv i =>
    intro Δ η A ht m Γ e σ hs hh hm
    cases ht with
    | var _ hi =>
      obtain ⟨k, hk⟩ := denoteSubstitution_lookup_exists M K
        E N p hs hh i hi
      refine ⟨k.effectMono le_sup_left, ?_⟩
      have he := Models.denote_effectMono (algebra M.toSeqData K) k
        (show e ≤ e ⊔ η from le_sup_left)
      change p.orient M.le _ (denote M.toSeqData K (k.effectMono le_sup_left))
      exact (congrArg (fun f => p.orient M.le
        (M.compose (denoteSubstitution M.toSeqData K hs)
          («variable» M.toSeqData i hi)) f) he).mpr hk
  | op f a ih =>
    intro Δ η A ht m Γ e σ hs hh hm
    cases ht with
    | op hf ha =>
      obtain ⟨k, hk⟩ := ih ha hs hh hm
      refine ⟨.op (hf.trans le_sup_right) k, ?_⟩
      change p.orient M.le
        (M.compose (denoteSubstitution M.toSeqData K hs)
          (M.compose (denote M.toSeqData K ha) (M.instruction f)))
        (M.compose (denote M.toSeqData K k) (M.instruction f))
      simpa only [M.toSeqData.compose_assoc] using
        M.toSeqData.orient_compose_right p hk (M.instruction f)
  | unit =>
    intro Δ η A ht m Γ e σ hs hh hm
    cases ht with
    | unit hd =>
      exact ⟨.unit (hs.discardable hd),
        denoteSubstitution_discard M K E p hs hh hd⟩
  | pair a b iha ihb =>
    intro Δ η A ht m Γ e σ hs hh hm
    cases ht with
    | pair sd ha hb =>
      obtain ⟨Γl, Γr, sg, sl, sr, hl, hr, _, he⟩ :=
        denoteSubstitution_split_exists M K E p hs hh sd
      obtain ⟨ka, hea⟩ := iha ha sl hl hm
      obtain ⟨kb, heb⟩ := ihb hb sr hr hm
      refine ⟨.pair sg ka kb, ?_⟩
      change p.orient M.le
        (M.compose (denoteSubstitution M.toSeqData K hs)
          (M.compose (split M.toSeqData sd) (M.tensor (denote M.toSeqData K ha) (denote M.toSeqData K hb))))
        (M.compose (split M.toSeqData sg) (M.tensor (denote M.toSeqData K ka) (denote M.toSeqData K kb)))
      have h1 := M.toSeqData.orient_compose_right p he (M.tensor (denote M.toSeqData K ha) (denote M.toSeqData K hb))
      have h2 := M.toSeqData.orient_compose_left p
        (M.toSeqData.tensor_comp_mover p
          (denoteSubstitution M.toSeqData K sl)
          (denoteSubstitution M.toSeqData K sr)
          (denote M.toSeqData K ha) (denote M.toSeqData K hb) hm
          (denoteSubstitution_effect M.toSeqData K E sr)
          (denote_effect K E ha)) (split M.toSeqData sg)
      have h3 := M.toSeqData.orient_compose_left p (M.toSeqData.orient_tensor p hea heb)
        (split M.toSeqData sg)
      exact M.toSeqData.orient_trans p
        (by simpa only [M.toSeqData.compose_assoc] using h1)
        (M.toSeqData.orient_trans p h2 h3)
  | let₁ a b iha ihb =>
    intro Δ η B ht m Γ e σ hs hh hm
    cases ht with
    | @let₁ n Δ Δl Δr η a b A B sd ha hb =>
      obtain ⟨Γr, Γl, sg, sr, sl, hr, hl, _, he⟩ :=
        denoteSubstitution_split_exists M K E p hs hh sd.symm
      obtain ⟨ka, hea⟩ := iha ha sr hr hm
      obtain ⟨hbn, hbnEq⟩ := denote_normalizeBinder_exists M K N hb
      obtain ⟨su, hu, hue⟩ := denoteSubstitution_up_exists M K
        N p sl hl A
      obtain ⟨kb, heb⟩ := ihb hbn su hu hm
      have hebody : M.compose (denoteSubstitution M.toSeqData K su) (denote M.toSeqData K hbn) =
          M.compose (M.right (denoteSubstitution M.toSeqData K sl) A) (denote M.toSeqData K hb) :=
        congrArg₂ (fun (f : M.Hom (product (packed Γl) A) (product (packed Δl) A))
          (g : M.Hom (product (packed Δl) A) B) => M.compose f g) hue hbnEq
      replace heb := (congrArg (fun f => p.orient M.le f (denote M.toSeqData K kb)) hebody).mp heb
      refine ⟨.let₁ sg.symm ka kb, ?_⟩
      let bsem : M.Hom (product (packed Δl) A) B := denote M.toSeqData K hb
      have h1 := M.toSeqData.orient_compose_right p he
        (M.compose (M.braiding (packed Δr) (packed Δl))
          (M.compose (M.left (packed Δl) (denote M.toSeqData K ha)) bsem))
      simp only [M.toSeqData.compose_assoc] at h1
      rw [← M.toSeqData.compose_assoc (split M.toSeqData sd.symm), split_symm] at h1
      have h2 := M.toSeqData.orient_compose_left p
        (M.toSeqData.tensor_bind_mover p
          (denoteSubstitution M.toSeqData K sr)
          (denoteSubstitution M.toSeqData K sl)
          (denote M.toSeqData K ha) bsem hm
          (denoteSubstitution_effect M.toSeqData K E sl)
          (denote_effect K E ha)) (split M.toSeqData sg)
      rw [← M.toSeqData.compose_assoc (split M.toSeqData sg) (M.braiding (packed Γr) (packed Γl)), split_symm] at h2
      have h3 := M.toSeqData.orient_compose_left p
        (M.toSeqData.orient_compose p (M.toSeqData.orient_left p (packed Γl) hea) heb)
        (split M.toSeqData sg.symm)
      exact M.toSeqData.orient_trans p h1 (M.toSeqData.orient_trans p h2 h3)
  | let₂ a b iha ihb =>
    intro Δ η C ht m Γ e σ hs hh hm
    cases ht with
    | @let₂ n Δ Δl Δr η a b A B C sd ha hb =>
      obtain ⟨Γr, Γl, sg, sr, sl, hr, hl, _, he⟩ :=
        denoteSubstitution_split_exists M K E p hs hh sd.symm
      obtain ⟨ka, hea⟩ := iha ha sr hr hm
      obtain ⟨hbn, hbnEq⟩ := denote_normalizeBinders₂_exists M K
        N hb
      obtain ⟨su, hu, hue⟩ := denoteSubstitution_up_exists M K
        N p sl hl A
      obtain ⟨suu, huu, huue⟩ := denoteSubstitution_up_exists M K
        N p su hu B
      obtain ⟨kb, heb⟩ := ihb hbn suu huu hm
      have heup : denoteSubstitution M.toSeqData K suu =
          M.right (M.right (denoteSubstitution M.toSeqData K sl) A) B :=
        huue.trans (congrArg (fun f : M.Hom (product (packed Γl) A) (product (packed Δl) A) => M.right f B) hue)
      have hebody : M.compose (denoteSubstitution M.toSeqData K suu) (denote M.toSeqData K hbn) =
          M.compose (M.right (M.right (denoteSubstitution M.toSeqData K sl) A) B)
            (denote M.toSeqData K hb) :=
        congrArg₂ (fun (f : M.Hom (product (product (packed Γl) A) B) (product (product (packed Δl) A) B))
          (g : M.Hom (product (product (packed Δl) A) B) C) => M.compose f g) heup hbnEq
      replace heb := (congrArg (fun f => p.orient M.le f (denote M.toSeqData K kb)) hebody).mp heb
      refine ⟨.let₂ sg.symm ka kb, ?_⟩
      let bsem : M.Hom (product (product (packed Δl) A) B) C := denote M.toSeqData K hb
      have h1 := M.toSeqData.orient_compose_right p he
        (M.compose (M.braiding (packed Δr) (packed Δl))
          (M.compose (M.left (packed Δl) (denote M.toSeqData K ha))
            (M.compose (M.associatorInv (packed Δl) A B) bsem)))
      simp only [M.toSeqData.compose_assoc] at h1
      rw [← M.toSeqData.compose_assoc (split M.toSeqData sd.symm), split_symm] at h1
      have h2 := M.toSeqData.orient_compose_left p
        (M.toSeqData.tensor_bind_mover p
          (denoteSubstitution M.toSeqData K sr)
          (denoteSubstitution M.toSeqData K sl)
          (denote M.toSeqData K ha) (M.compose (M.associatorInv (packed Δl) A B) bsem) hm
          (denoteSubstitution_effect M.toSeqData K E sl)
          (denote_effect K E ha)) (split M.toSeqData sg)
      rw [← M.toSeqData.compose_assoc (split M.toSeqData sg) (M.braiding (packed Γr) (packed Γl)), split_symm] at h2
      rw [← M.toSeqData.compose_assoc (M.right _ (product A B)),
        M.toSeqData.associatorInv_natural_left] at h2
      simp only [M.toSeqData.compose_assoc] at h2
      have h3 := M.toSeqData.orient_compose_left p
        (M.toSeqData.orient_compose p (M.toSeqData.orient_left p (packed Γl) hea)
          (M.toSeqData.orient_compose_left p heb (M.associatorInv (packed Γl) A B)))
        (split M.toSeqData sg.symm)
      exact M.toSeqData.orient_trans p h1 (M.toSeqData.orient_trans p h2 h3)
  | inl a ih =>
    intro Δ η A ht m Γ e σ hs hh hm
    cases ht with
    | inl hf ha =>
      obtain ⟨k, hk⟩ := ih ha hs hh hm
      refine ⟨.inl hf k, ?_⟩
      change p.orient M.le
        (M.compose (denoteSubstitution M.toSeqData K hs)
          (M.compose (denote M.toSeqData K ha) (K.inl hf _ _)))
        (M.compose (denote M.toSeqData K k) (K.inl hf _ _))
      simpa only [M.toSeqData.compose_assoc] using
        M.toSeqData.orient_compose_right p hk (K.inl hf _ _)
  | inr a ih =>
    intro Δ η A ht m Γ e σ hs hh hm
    cases ht with
    | inr hf ha =>
      obtain ⟨k, hk⟩ := ih ha hs hh hm
      refine ⟨.inr hf k, ?_⟩
      change p.orient M.le
        (M.compose (denoteSubstitution M.toSeqData K hs)
          (M.compose (denote M.toSeqData K ha) (K.inr hf _ _)))
        (M.compose (denote M.toSeqData K k) (K.inr hf _ _))
      simpa only [M.toSeqData.compose_assoc] using
        M.toSeqData.orient_compose_right p hk (K.inr hf _ _)
  | case a l r iha ihl ihr =>
    intro Δ η C ht m Γ e σ hs hh hm
    cases ht with
    | @case n Δ Δl Δr η a l r A B C hf sd ha hl hr =>
      obtain ⟨Γr, Γl, sg, sr, sl, hrg, hlg, _, he⟩ :=
        denoteSubstitution_split_exists M K E p hs hh sd.symm
      obtain ⟨ka, hea⟩ := iha ha sr hrg hm
      obtain ⟨hln, hlne⟩ := denote_normalizeBinder_exists M K N hl
      obtain ⟨hrn, hrne⟩ := denote_normalizeBinder_exists M K N hr
      obtain ⟨suA, huA, hueA⟩ := denoteSubstitution_up_exists M K N p sl hlg A
      obtain ⟨suB, huB, hueB⟩ := denoteSubstitution_up_exists M K N p sl hlg B
      obtain ⟨kl, hel⟩ := ihl hln suA huA hm
      obtain ⟨kr, her⟩ := ihr hrn suB huB hm
      have hel' : M.compose (denoteSubstitution M.toSeqData K suA) (denote M.toSeqData K hln) =
          M.compose (M.right (denoteSubstitution M.toSeqData K sl) A) (denote M.toSeqData K hl) :=
        congrArg₂ (fun (f : M.Hom (product (packed Γl) A) (product (packed Δl) A))
          (g : M.Hom (product (packed Δl) A) C) => M.compose f g) hueA hlne
      have her' : M.compose (denoteSubstitution M.toSeqData K suB) (denote M.toSeqData K hrn) =
          M.compose (M.right (denoteSubstitution M.toSeqData K sl) B) (denote M.toSeqData K hr) :=
        congrArg₂ (fun (f : M.Hom (product (packed Γl) B) (product (packed Δl) B))
          (g : M.Hom (product (packed Δl) B) C) => M.compose f g) hueB hrne
      replace hel := (congrArg (fun f => p.orient M.le f (denote M.toSeqData K kl)) hel').mp hel
      replace her := (congrArg (fun f => p.orient M.le f (denote M.toSeqData K kr)) her').mp her
      refine ⟨.case hf sg.symm ka kl kr, ?_⟩
      let bsem : M.Hom (product (packed Δl) (coprod A B)) C :=
        M.compose (K.distribute hf (packed Δl) A B) (K.desc hf (denote M.toSeqData K hl) (denote M.toSeqData K hr))
      have h1 := M.toSeqData.orient_compose_right p he
        (M.compose (M.braiding (packed Δr) (packed Δl))
          (M.compose (M.left (packed Δl) (denote M.toSeqData K ha)) bsem))
      simp only [M.toSeqData.compose_assoc] at h1
      rw [← M.toSeqData.compose_assoc (split M.toSeqData sd.symm), split_symm] at h1
      have h2 := M.toSeqData.orient_compose_left p
        (M.toSeqData.tensor_bind_mover p
          (denoteSubstitution M.toSeqData K sr) (denoteSubstitution M.toSeqData K sl)
          (denote M.toSeqData K ha) bsem hm
          (denoteSubstitution_effect M.toSeqData K E sl) (denote_effect K E ha))
        (split M.toSeqData sg)
      rw [← M.toSeqData.compose_assoc (split M.toSeqData sg) (M.braiding (packed Γr) (packed Γl)), split_symm] at h2
      have hbranch : p.orient M.le
          (K.desc hf
            (M.compose (M.right (denoteSubstitution M.toSeqData K sl) A) (denote M.toSeqData K hl))
            (M.compose (M.right (denoteSubstitution M.toSeqData K sl) B) (denote M.toSeqData K hr)))
          (K.desc hf (denote M.toSeqData K kl) (denote M.toSeqData K kr)) := by
        cases p <;> exact O.desc hf hel her
      have h3 := M.toSeqData.orient_compose_left p
        (M.toSeqData.orient_compose p (M.toSeqData.orient_left p (packed Γl) hea)
          (M.toSeqData.orient_compose_left p hbranch (K.distribute hf (packed Γl) A B)))
        (split M.toSeqData sg.symm)
      have hn := N.case_natural hf (denoteSubstitution M.toSeqData K sl)
        (denote M.toSeqData K hl) (denote M.toSeqData K hr)
      change M.compose (M.right (denoteSubstitution M.toSeqData K sl) (coprod A B)) bsem = _ at hn
      rw [hn] at h2
      exact M.toSeqData.orient_trans p h1 (M.toSeqData.orient_trans p h2 h3)
  | abort a ih =>
    intro Δ η A ht m Γ e σ hs hh hm
    cases ht with
    | abort hf ha =>
      obtain ⟨k, hk⟩ := ih ha hs hh hm
      refine ⟨.abort hf k, ?_⟩
      change p.orient M.le
        (M.compose (denoteSubstitution M.toSeqData K hs)
          (M.compose (denote M.toSeqData K ha) (K.abort hf _)))
        (M.compose (denote M.toSeqData K k) (K.abort hf _))
      simpa only [M.toSeqData.compose_assoc] using
        M.toSeqData.orient_compose_right p hk (K.abort hf _)
  | iter a b iha ihb => exact loop a b iha ihb

end Silmaril.Isotope.Refinement.Models.Denotation
