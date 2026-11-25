module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.TypingComparison

/-! # Constructor rules for common semantic typings -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
open CategoryTheory
universe u v w r
variable {α : Type u} [DecidableEq α] [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : CaseData.{u,v,w,r} (Ty α) Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F)

set_option backward.isDefEq.respectTransparency false in
/-- Pairing respects a common typing whenever both component supports align. -/
theorem TypingComparison.pair {n : Nat} {Γ Γl Γr Δ Δl Δr : QCtx (Ty α) n} {e e' : ε}
    {a b : Term Φ n} {A B C D : Ty α}
    (s : QCtx.Split Γ Γl Γr) (t : QCtx.Split Δ Δl Δr)
    (hc : QCtx.Aligned Γ Δ) (hl : QCtx.Aligned Γl Δl) (hr : QCtx.Aligned Γr Δr)
    (ha : HasType F Γl e a A) (hb : HasType F Γr e b B)
    (ka : HasType F Δl e' a C) (kb : HasType F Δr e' b D)
    (ca : TypingComparison M K ha ka hl) (cb : TypingComparison M K hb kb hr) :
    TypingComparison M K (.pair s ha hb) (.pair t ka kb) hc := by
  obtain ⟨la, hla, kla⟩ := ca
  obtain ⟨lb, hlb, klb⟩ := cb
  refine ⟨.pair (s.merge t hl hr) la lb, ?_, ?_⟩
  · change M.compose (M.compose (split M.toSeqData s)
      (M.tensor (denote M.toSeqData K ha) (denote M.toSeqData K hb)))
      (M.tensor (mergeLeft M A C) (mergeLeft M B D)) =
      M.compose (mergeContext M Γ Δ hc).1.1
        (M.compose (split M.toSeqData (s.merge t hl hr))
          (M.tensor (denote M.toSeqData K la) (denote M.toSeqData K lb)))
    rw [M.compose_assoc, M.toSeqData.tensor_comp_pure_middle _ _ _ _ (mergeLeft_pure M A C), hla, hlb,
      ← M.toSeqData.tensor_comp_pure _ _ _ _ (mergeContext M Γr Δr hr).1.2]
    simp only [← M.compose_assoc]
    exact congrArg (fun f => M.compose f (M.tensor (denote M.toSeqData K la) (denote M.toSeqData K lb)))
      (congrArg Subtype.val (mergeContext_split_fst M s t hc hl hr)).symm
  · change M.compose (M.compose (split M.toSeqData t)
      (M.tensor (denote M.toSeqData K ka) (denote M.toSeqData K kb)))
      (M.tensor (mergeRight M A C) (mergeRight M B D)) =
      M.compose (mergeContext M Γ Δ hc).2.1
        (M.compose (split M.toSeqData (s.merge t hl hr))
          (M.tensor (denote M.toSeqData K la) (denote M.toSeqData K lb)))
    rw [M.compose_assoc, M.toSeqData.tensor_comp_pure_middle _ _ _ _ (mergeRight_pure M A C), kla, klb,
      ← M.toSeqData.tensor_comp_pure _ _ _ _ (mergeContext M Γr Δr hr).2.2]
    simp only [← M.compose_assoc]
    exact congrArg (fun f => M.compose f (M.tensor (denote M.toSeqData K la) (denote M.toSeqData K lb)))
      (congrArg Subtype.val (mergeContext_split_snd M s t hc hl hr)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Canonical raw supports remove the alignment obligation on pairing's chosen splits. -/
theorem TypingComparison.pair_support (N : ControlEnvironment K)
    {n : Nat} {Γ Γl Γr Δ Δl Δr : QCtx (Ty α) n} {e e' : ε}
    {a b : Term Φ n} {A B C D : Ty α}
    (s : QCtx.Split Γ Γl Γr) (t : QCtx.Split Δ Δl Δr) (hc : QCtx.Aligned Γ Δ)
    (ha : HasType F Γl e a A) (hb : HasType F Γr e b B)
    (ka : HasType F Δl e' a C) (kb : HasType F Δr e' b D)
    (ca : TypingComparison M K ha.support ka.support (ha.support_aligned ka))
    (cb : TypingComparison M K hb.support kb.support (hb.support_aligned kb)) :
    TypingComparison M K (.pair s ha hb) (.pair t ka kb) hc := by
  let p := fun i => Term.uses a i || Term.uses b i
  let sc := s.restrictOutputs (Term.uses a) (Term.uses b)
    (fun _ => ha.used_nonzero) (fun _ => hb.used_nonzero)
  let tc := t.restrictOutputs (Term.uses a) (Term.uses b)
    (fun _ => ka.used_nonzero) (fun _ => kb.used_nonzero)
  let h : HasType F Γ e (.pair a b) (Ty.product A B) := .pair s ha hb
  let k : HasType F Δ e' (.pair a b) (Ty.product C D) := .pair t ka kb
  let hn := HasType.pair sc ha.support hb.support
  let kn := HasType.pair tc ka.support kb.support
  let w := h.supportWeakening
  let v := k.supportWeakening
  let wm := QCtx.weakening_merge_restrict Γ Δ p (fun i => (h.slotAllows i).2) (fun i => (k.slotAllows i).2)
  have eh : denote M.toSeqData K h = M.compose (weaken M.toSeqData w) (denote M.toSeqData K hn) := by
    change M.compose (split M.toSeqData s) (M.tensor (denote M.toSeqData K ha) (denote M.toSeqData K hb)) =
      M.compose (weaken M.toSeqData w)
        (M.compose (split M.toSeqData sc) (M.tensor (denote M.toSeqData K ha.support) (denote M.toSeqData K hb.support)))
    rw [denote_restrict M.toSeqModel K N ha _ (fun _ => id), denote_restrict M.toSeqModel K N hb _ (fun _ => id),
      ← M.toSeqData.tensor_comp_pure _ _ _ _ (weaken_pure _ hb.supportWeakening)]
    simp only [← M.compose_assoc]
    exact congrArg (fun f => M.compose f (M.tensor (denote M.toSeqData K ha.support) (denote M.toSeqData K hb.support)))
      (weaken_split M.toSeqModel w s sc ha.supportWeakening hb.supportWeakening).symm
  have ek : denote M.toSeqData K k = M.compose (weaken M.toSeqData v) (denote M.toSeqData K kn) := by
    change M.compose (split M.toSeqData t) (M.tensor (denote M.toSeqData K ka) (denote M.toSeqData K kb)) =
      M.compose (weaken M.toSeqData v)
        (M.compose (split M.toSeqData tc) (M.tensor (denote M.toSeqData K ka.support) (denote M.toSeqData K kb.support)))
    rw [denote_restrict M.toSeqModel K N ka _ (fun _ => id), denote_restrict M.toSeqModel K N kb _ (fun _ => id),
      ← M.toSeqData.tensor_comp_pure _ _ _ _ (weaken_pure _ kb.supportWeakening)]
    simp only [← M.compose_assoc]
    exact congrArg (fun f => M.compose f (M.tensor (denote M.toSeqData K ka.support) (denote M.toSeqData K kb.support)))
      (weaken_split M.toSeqModel v t tc ka.supportWeakening kb.supportWeakening).symm
  exact TypingComparison.of_factors M K N h k hn kn w v wm hc (hc.restrict p) eh ek
    (TypingComparison.pair M K sc tc (hc.restrict p) (ha.support_aligned ka) (hb.support_aligned kb)
      ha.support hb.support ka.support kb.support ca cb)

omit [DecidableEq α] in
/-- Move a pure environment comparison before an effectful right computation. -/
private theorem left_tensor_pure {L E X A B : Ty α} (u : M.Hom L E) (hu : M.hasEffect ⊥ u)
    (f : M.Hom X A) (a : M.Hom A B) :
    M.compose (M.left L f) (M.tensor u a) = M.tensor u (M.compose f a) := by
  unfold SeqData.tensor
  rw [← M.compose_assoc, ← M.toSeqData.exchange_left_pure u f hu, M.compose_assoc, ← M.left_compose]

omit [DecidableEq α] in
/-- The right computation of a tensor can always continue in place. -/
private theorem tensor_left {L E X A B : Ty α} (u : M.Hom L E) (f : M.Hom X A) (a : M.Hom A B) :
    M.compose (M.tensor u f) (M.left E a) = M.tensor u (M.compose f a) := by
  simp only [SeqData.tensor, M.left_compose, M.compose_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Let binding combines pure comparisons of its environment, bound type, and result. -/
theorem TypingComparison.let₁ {n : Nat} {Γ Γl Γr Δ Δl Δr : QCtx (Ty α) n} {e e' : ε}
    {a : Term Φ n} {b : Term Φ (n+1)} {A B C D : Ty α}
    (s : QCtx.Split Γ Γl Γr) (t : QCtx.Split Δ Δl Δr)
    (hc : QCtx.Aligned Γ Δ) (hl : QCtx.Aligned Γl Δl) (hr : QCtx.Aligned Γr Δr)
    (hbctx : QCtx.Aligned (Γl.snoc A) (Δl.snoc C))
    (ha : HasType F Γr e a A) (hb : HasType F (Γl.snoc A) e b B)
    (ka : HasType F Δr e' a C) (kb : HasType F (Δl.snoc C) e' b D)
    (ca : TypingComparison M K ha ka hr) (cb : TypingComparison M K hb kb hbctx) :
    TypingComparison M K (.let₁ s ha hb) (.let₁ t ka kb) hc := by
  obtain ⟨la, hla, kla⟩ := ca
  obtain ⟨lb, hlb, klb⟩ := cb
  have he : QCtx.merge (Γl.snoc A) (Δl.snoc C) = (QCtx.merge Γl Δl).snoc (mergeType A C) := by
    simp
  let lb' := lb.castContext he
  have eb : denote M.toSeqData K lb' = denote M.toSeqData K lb :=
    eq_of_heq (denote_castContext_heq M.toSeqData K lb he)
  refine ⟨.let₁ (s.merge t hl hr) la lb', ?_, ?_⟩
  · change M.compose (denote M.toSeqData K hb) (mergeLeft M B D) =
      M.compose (M.tensor (mergeContext M Γl Δl hl).1.1 (mergeLeft M A C)) (denote M.toSeqData K lb) at hlb
    change M.compose (M.compose (split M.toSeqData s)
      (M.compose (M.left _ (denote M.toSeqData K ha)) (denote M.toSeqData K hb))) (mergeLeft M B D) =
      M.compose (mergeContext M Γ Δ hc).1.1
        (M.compose (split M.toSeqData (s.merge t hl hr))
          (M.compose (M.left _ (denote M.toSeqData K la)) (denote M.toSeqData K lb')))
    simp only [M.compose_assoc]
    rw [hlb, ← M.compose_assoc (M.left _ (denote M.toSeqData K ha)),
      left_tensor_pure M _ (mergeContext M Γl Δl hl).1.2, hla,
      ← tensor_left M, eb]
    simp only [← M.compose_assoc]
    exact congrArg (fun f => M.compose (M.compose f (M.left _ (denote M.toSeqData K la))) (denote M.toSeqData K lb))
      (congrArg Subtype.val (mergeContext_split_fst M s t hc hl hr)).symm
  · change M.compose (denote M.toSeqData K kb) (mergeRight M B D) =
      M.compose (M.tensor (mergeContext M Γl Δl hl).2.1 (mergeRight M A C)) (denote M.toSeqData K lb) at klb
    change M.compose (M.compose (split M.toSeqData t)
      (M.compose (M.left _ (denote M.toSeqData K ka)) (denote M.toSeqData K kb))) (mergeRight M B D) =
      M.compose (mergeContext M Γ Δ hc).2.1
        (M.compose (split M.toSeqData (s.merge t hl hr))
          (M.compose (M.left _ (denote M.toSeqData K la)) (denote M.toSeqData K lb')))
    simp only [M.compose_assoc]
    rw [klb, ← M.compose_assoc (M.left _ (denote M.toSeqData K ka)),
      left_tensor_pure M _ (mergeContext M Γl Δl hl).2.2, kla,
      ← tensor_left M, eb]
    simp only [← M.compose_assoc]
    exact congrArg (fun f => M.compose (M.compose f (M.left _ (denote M.toSeqData K la))) (denote M.toSeqData K lb))
      (congrArg Subtype.val (mergeContext_split_snd M s t hc hl hr)).symm

omit [DecidableEq α] in
/-- Pure comparisons respect the associator used by product elimination. -/
private theorem comparison_associatorInv {L E A C B D : Ty α}
    (f : PureHom M.toSeqData L E) (a : PureHom M.toSeqData A C) (b : PureHom M.toSeqData B D) :
    M.compose (M.associatorInv L A B) (M.tensor (M.tensor f.1 a.1) b.1) =
      M.compose (M.tensor f.1 (M.tensor a.1 b.1)) (M.associatorInv E C D) := by
  let f' : (⟨L⟩ : M.toSeqData.PureObject) ⟶ (⟨E⟩ : M.toSeqData.PureObject) := f
  let a' : (⟨A⟩ : M.toSeqData.PureObject) ⟶ (⟨C⟩ : M.toSeqData.PureObject) := a
  let b' : (⟨B⟩ : M.toSeqData.PureObject) ⟶ (⟨D⟩ : M.toSeqData.PureObject) := b
  exact (congrArg Subtype.val (CategoryTheory.MonoidalCategory.associator_inv_naturality f' a' b')).symm

set_option backward.isDefEq.respectTransparency false in
/-- Product binding compares both hidden component types in its common body context. -/
theorem TypingComparison.let₂ {n : Nat} {Γ Γl Γr Δ Δl Δr : QCtx (Ty α) n} {e e' : ε}
    {a : Term Φ n} {b : Term Φ (n+2)} {A B C D E G : Ty α}
    (s : QCtx.Split Γ Γl Γr) (t : QCtx.Split Δ Δl Δr)
    (hc : QCtx.Aligned Γ Δ) (hl : QCtx.Aligned Γl Δl) (hr : QCtx.Aligned Γr Δr)
    (hbctx : QCtx.Aligned ((Γl.snoc A).snoc B) ((Δl.snoc C).snoc D))
    (ha : HasType F Γr e a (.product A B)) (hb : HasType F ((Γl.snoc A).snoc B) e b E)
    (ka : HasType F Δr e' a (.product C D)) (kb : HasType F ((Δl.snoc C).snoc D) e' b G)
    (ca : TypingComparison M K ha ka hr) (cb : TypingComparison M K hb kb hbctx) :
    TypingComparison M K (.let₂ s ha hb) (.let₂ t ka kb) hc := by
  obtain ⟨la, hla, kla⟩ := ca
  obtain ⟨lb, hlb, klb⟩ := cb
  let da : M.Hom (packed Γr) (product A B) := denote M.toSeqData K ha
  let dk : M.Hom (packed Δr) (product C D) := denote M.toSeqData K ka
  let dm : M.Hom (packed (QCtx.merge Γr Δr)) (product (mergeType A C) (mergeType B D)) := denote M.toSeqData K la
  change M.compose da (M.tensor (mergeLeft M A C) (mergeLeft M B D)) =
    M.compose (mergeContext M Γr Δr hr).1.1 dm at hla
  change M.compose dk (M.tensor (mergeRight M A C) (mergeRight M B D)) =
    M.compose (mergeContext M Γr Δr hr).2.1 dm at kla
  have he : QCtx.merge ((Γl.snoc A).snoc B) ((Δl.snoc C).snoc D) =
      ((QCtx.merge Γl Δl).snoc (mergeType A C)).snoc (mergeType B D) := by simp
  let lb' := lb.castContext he
  have eb : denote M.toSeqData K lb' = denote M.toSeqData K lb :=
    eq_of_heq (denote_castContext_heq M.toSeqData K lb he)
  rw [← eb] at hlb klb
  let db : M.Hom (product (product (packed (QCtx.merge Γl Δl)) (mergeType A C)) (mergeType B D))
      (mergeType E G) := denote M.toSeqData K lb'
  refine ⟨.let₂ (s.merge t hl hr) la lb', ?_, ?_⟩
  · change M.compose (denote M.toSeqData K hb) (mergeLeft M E G) =
      M.compose (M.tensor (M.tensor (mergeContext M Γl Δl hl).1.1 (mergeLeft M A C)) (mergeLeft M B D))
        db at hlb
    change M.compose (M.compose (split M.toSeqData s)
      (M.compose (M.left _ da)
        (M.compose (M.associatorInv _ A B) (denote M.toSeqData K hb)))) (mergeLeft M E G) =
      M.compose (mergeContext M Γ Δ hc).1.1
        (M.compose (split M.toSeqData (s.merge t hl hr))
          (M.compose (M.left _ dm)
            (M.compose (M.associatorInv _ (mergeType A C) (mergeType B D)) db)))
    simp only [M.compose_assoc]
    have hs := comparison_associatorInv M (mergeContext M Γl Δl hl).1 (mergeArrows M A C).1 (mergeArrows M B D).1
    change M.compose (M.associatorInv (packed Γl) A B)
      (M.tensor (M.tensor (mergeContext M Γl Δl hl).1.1 (mergeLeft M A C)) (mergeLeft M B D)) =
      M.compose (M.tensor (mergeContext M Γl Δl hl).1.1 (M.tensor (mergeLeft M A C) (mergeLeft M B D)))
        (M.associatorInv (packed (QCtx.merge Γl Δl)) (mergeType A C) (mergeType B D)) at hs
    rw [hlb, ← M.compose_assoc (M.associatorInv _ A B), hs]
    simp only [M.compose_assoc]
    rw [← M.compose_assoc (M.left _ da),
      left_tensor_pure M _ (mergeContext M Γl Δl hl).1.2, hla, ← tensor_left M]
    simp only [← M.compose_assoc]
    exact congrArg (fun f => M.compose (M.compose (M.compose f (M.left _ dm))
      (M.associatorInv _ (mergeType A C) (mergeType B D))) db)
      (congrArg Subtype.val (mergeContext_split_fst M s t hc hl hr)).symm
  · change M.compose (denote M.toSeqData K kb) (mergeRight M E G) =
      M.compose (M.tensor (M.tensor (mergeContext M Γl Δl hl).2.1 (mergeRight M A C)) (mergeRight M B D))
        db at klb
    change M.compose (M.compose (split M.toSeqData t)
      (M.compose (M.left _ dk)
        (M.compose (M.associatorInv _ C D) (denote M.toSeqData K kb)))) (mergeRight M E G) =
      M.compose (mergeContext M Γ Δ hc).2.1
        (M.compose (split M.toSeqData (s.merge t hl hr))
          (M.compose (M.left _ dm)
            (M.compose (M.associatorInv _ (mergeType A C) (mergeType B D)) db)))
    simp only [M.compose_assoc]
    have hs := comparison_associatorInv M (mergeContext M Γl Δl hl).2 (mergeArrows M A C).2 (mergeArrows M B D).2
    change M.compose (M.associatorInv (packed Δl) C D)
      (M.tensor (M.tensor (mergeContext M Γl Δl hl).2.1 (mergeRight M A C)) (mergeRight M B D)) =
      M.compose (M.tensor (mergeContext M Γl Δl hl).2.1 (M.tensor (mergeRight M A C) (mergeRight M B D)))
        (M.associatorInv (packed (QCtx.merge Γl Δl)) (mergeType A C) (mergeType B D)) at hs
    rw [klb, ← M.compose_assoc (M.associatorInv _ C D), hs]
    simp only [M.compose_assoc]
    rw [← M.compose_assoc (M.left _ dk),
      left_tensor_pure M _ (mergeContext M Γl Δl hl).2.2, kla, ← tensor_left M]
    simp only [← M.compose_assoc]
    exact congrArg (fun f => M.compose (M.compose (M.compose f (M.left _ dm))
      (M.associatorInv _ (mergeType A C) (mergeType B D))) db)
      (congrArg Subtype.val (mergeContext_split_snd M s t hc hl hr)).symm

end Silmaril.Isotope.Refinement.Models.Denotation
