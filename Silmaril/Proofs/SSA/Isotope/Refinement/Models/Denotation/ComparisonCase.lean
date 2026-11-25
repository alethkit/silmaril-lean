module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ComparisonControl

/-! # Comparing contextual case typings

The common typing combines hidden summands and branch environments. The
categorical comparison is derived from coproduct extensionality and purity of
structural environment maps.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models
universe u v w r

section CaseMap
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : CaseData.{u,v,w,r} τ Φ ε)

/-- Simultaneous change of the ambient environment and the two summands of
contextual case analysis. Only the coproduct injections must be pure. -/
theorem CaseData.case_map {E G A B C D Z : τ}
    (u : M.Hom E G) (v : M.Hom A C) (w : M.Hom B D)
    (l : M.Hom (product G C) Z) (r : M.Hom (product G D) Z) :
    M.compose (M.tensor u (M.desc (M.compose v (M.inl C D)) (M.compose w (M.inr C D))))
      (M.compose (M.distribute G C D) (M.desc l r)) =
      M.compose (M.distribute E A B)
        (M.desc (M.compose (M.tensor u v) l) (M.compose (M.tensor u w) r)) := by
  apply M.distributed_hom_ext
  · simp only [SeqData.tensor, M.compose_assoc]
    rw [← M.compose_assoc (M.left E (M.inl A B)),
      ← M.toSeqData.exchange_right_pure u (M.inl A B) (M.inl_pure A B)]
    simp only [M.compose_assoc]
    rw [← M.compose_assoc (M.left G (M.inl A B)), ← M.left_compose, M.inl_desc,
      M.left_compose]
    simp only [M.compose_assoc]
    rw [← M.compose_assoc (M.left G (M.inl C D)), M.left_inl_distribute, M.inl_desc,
      ← M.compose_assoc (M.left E (M.inl A B)), M.left_inl_distribute, M.inl_desc]
  · simp only [SeqData.tensor, M.compose_assoc]
    rw [← M.compose_assoc (M.left E (M.inr A B)),
      ← M.toSeqData.exchange_right_pure u (M.inr A B) (M.inr_pure A B)]
    simp only [M.compose_assoc]
    rw [← M.compose_assoc (M.left G (M.inr A B)), ← M.left_compose, M.inr_desc,
      M.left_compose]
    simp only [M.compose_assoc]
    rw [← M.compose_assoc (M.left G (M.inr C D)), M.left_inr_distribute, M.inr_desc,
      ← M.compose_assoc (M.left E (M.inr A B)), M.left_inr_distribute, M.inr_desc]

end CaseMap
namespace Denotation
variable {α : Type u} [DecidableEq α] [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : CaseData.{u,v,w,r} (Ty α) Φ ε) {F : Fragment}
variable (it : F.HasIter → ∀ {A B : Ty α}, M.Hom A (coprod B A) → M.Hom A B)
local notation "K" => ControlData.ofCase M F it

omit [DecidableEq α] in
private theorem left_tensor_pure {L E X A B : Ty α} (u : M.Hom L E) (hu : M.hasEffect ⊥ u)
    (f : M.Hom X A) (a : M.Hom A B) :
    M.compose (M.left L f) (M.tensor u a) = M.tensor u (M.compose f a) := by
  unfold SeqData.tensor
  rw [← M.compose_assoc, ← M.toSeqData.exchange_left_pure u f hu, M.compose_assoc, ← M.left_compose]

omit [DecidableEq α] in
private theorem tensor_left {L E X A B : Ty α} (u : M.Hom L E) (f : M.Hom X A) (a : M.Hom A B) :
    M.compose (M.tensor u f) (M.left E a) = M.tensor u (M.compose f a) := by
  simp only [SeqData.tensor, M.left_compose, M.compose_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Case binding compares both hidden summands and both branch derivations. -/
theorem TypingComparison.case {n : Nat} {Γ Γl Γr Δ Δl Δr : QCtx (Ty α) n} {e e' : ε}
    {a : Term Φ n} {l r : Term Φ (n+1)} {A B C D E G : Ty α}
    (cap : F.HasCase) (s : QCtx.Split Γ Γl Γr) (t : QCtx.Split Δ Δl Δr)
    (hc : QCtx.Aligned Γ Δ) (hl : QCtx.Aligned Γl Δl) (hr : QCtx.Aligned Γr Δr)
    (hlctx : QCtx.Aligned (Γl.snoc A) (Δl.snoc C))
    (hrctx : QCtx.Aligned (Γl.snoc B) (Δl.snoc D))
    (ha : HasType F Γr e a (coprod A B)) (ka : HasType F Δr e' a (coprod C D))
    (hb : HasType F (Γl.snoc A) e l E) (kb : HasType F (Δl.snoc C) e' l G)
    (hd : HasType F (Γl.snoc B) e r E) (kd : HasType F (Δl.snoc D) e' r G)
    (ca : TypingComparison M K ha ka hr)
    (cb : TypingComparison M K hb kb hlctx) (cd : TypingComparison M K hd kd hrctx) :
    TypingComparison M K (.case cap s ha hb hd) (.case cap t ka kb kd) hc := by
  obtain ⟨la, hla, kla⟩ := ca
  obtain ⟨lb, hlb, klb⟩ := cb
  obtain ⟨ld, hld, kld⟩ := cd
  have he : QCtx.merge (Γl.snoc A) (Δl.snoc C) = (QCtx.merge Γl Δl).snoc (mergeType A C) := by simp
  have he' : QCtx.merge (Γl.snoc B) (Δl.snoc D) = (QCtx.merge Γl Δl).snoc (mergeType B D) := by simp
  let lb' := lb.castContext he
  let ld' := ld.castContext he'
  have eb : denote M.toSeqData K lb' = denote M.toSeqData K lb :=
    eq_of_heq (denote_castContext_heq M.toSeqData K lb he)
  have ed : denote M.toSeqData K ld' = denote M.toSeqData K ld :=
    eq_of_heq (denote_castContext_heq M.toSeqData K ld he')
  rw [← eb] at hlb klb
  rw [← ed] at hld kld
  change M.compose (denote M.toSeqData K ha)
    (M.desc (M.compose (mergeLeft M A C) (M.inl _ _)) (M.compose (mergeLeft M B D) (M.inr _ _))) =
      M.compose (mergeContext M Γr Δr hr).1.1 (denote M.toSeqData K la) at hla
  change M.compose (denote M.toSeqData K ka)
    (M.desc (M.compose (mergeRight M A C) (M.inl _ _)) (M.compose (mergeRight M B D) (M.inr _ _))) =
      M.compose (mergeContext M Γr Δr hr).2.1 (denote M.toSeqData K la) at kla
  refine ⟨.case cap (s.merge t hl hr) la lb' ld', ?_, ?_⟩
  · change M.compose (denote M.toSeqData K hb) (mergeLeft M E G) =
      M.compose (M.tensor (mergeContext M Γl Δl hl).1.1 (mergeLeft M A C)) (denote M.toSeqData K lb') at hlb
    change M.compose (denote M.toSeqData K hd) (mergeLeft M E G) =
      M.compose (M.tensor (mergeContext M Γl Δl hl).1.1 (mergeLeft M B D)) (denote M.toSeqData K ld') at hld
    change M.compose (M.compose (split M.toSeqData s)
      (M.compose (M.left _ (denote M.toSeqData K ha))
        (M.compose (M.distribute _ A B) (M.desc (denote M.toSeqData K hb) (denote M.toSeqData K hd))))) (mergeLeft M E G) =
      M.compose (mergeContext M Γ Δ hc).1.1
        (M.compose (split M.toSeqData (s.merge t hl hr))
          (M.compose (M.left _ (denote M.toSeqData K la))
            (M.compose (M.distribute _ _ _) (M.desc (denote M.toSeqData K lb') (denote M.toSeqData K ld')))))
    simp only [M.compose_assoc]
    rw [M.desc_compose, hlb, hld, ← M.case_map,
      ← M.compose_assoc (M.left _ (denote M.toSeqData K ha)),
      left_tensor_pure M _ (mergeContext M Γl Δl hl).1.2, hla,
      ← tensor_left M]
    simp only [← M.compose_assoc]
    exact congrArg (fun f => M.compose (M.compose (M.compose f (M.left (packed (QCtx.merge Γl Δl)) (denote M.toSeqData K la)))
      (M.distribute (packed (QCtx.merge Γl Δl)) (mergeType A C) (mergeType B D)))
        (M.desc (denote M.toSeqData K lb') (denote M.toSeqData K ld')))
      (congrArg Subtype.val (mergeContext_split_fst M s t hc hl hr)).symm
  · change M.compose (denote M.toSeqData K kb) (mergeRight M E G) =
      M.compose (M.tensor (mergeContext M Γl Δl hl).2.1 (mergeRight M A C)) (denote M.toSeqData K lb') at klb
    change M.compose (denote M.toSeqData K kd) (mergeRight M E G) =
      M.compose (M.tensor (mergeContext M Γl Δl hl).2.1 (mergeRight M B D)) (denote M.toSeqData K ld') at kld
    change M.compose (M.compose (split M.toSeqData t)
      (M.compose (M.left _ (denote M.toSeqData K ka))
        (M.compose (M.distribute _ C D) (M.desc (denote M.toSeqData K kb) (denote M.toSeqData K kd))))) (mergeRight M E G) =
      M.compose (mergeContext M Γ Δ hc).2.1
        (M.compose (split M.toSeqData (s.merge t hl hr))
          (M.compose (M.left _ (denote M.toSeqData K la))
            (M.compose (M.distribute _ _ _) (M.desc (denote M.toSeqData K lb') (denote M.toSeqData K ld')))))
    simp only [M.compose_assoc]
    rw [M.desc_compose, klb, kld, ← M.case_map,
      ← M.compose_assoc (M.left _ (denote M.toSeqData K ka)),
      left_tensor_pure M _ (mergeContext M Γl Δl hl).2.2, kla,
      ← tensor_left M]
    simp only [← M.compose_assoc]
    exact congrArg (fun f => M.compose (M.compose (M.compose f (M.left (packed (QCtx.merge Γl Δl)) (denote M.toSeqData K la)))
      (M.distribute (packed (QCtx.merge Γl Δl)) (mergeType A C) (mergeType B D)))
        (M.desc (denote M.toSeqData K lb') (denote M.toSeqData K ld')))
      (congrArg Subtype.val (mergeContext_split_snd M s t hc hl hr)).symm

end Denotation
end Silmaril.Isotope.Refinement.Models
