module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionTensor
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.SplitDistribution

/-! # Splitting the interpreted output of a quantitative substitution -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε)

/-- Split a substitution tail and send its last computation to the right. -/
theorem split_tensor_right {n : Nat} {Γ Γ12 Γ1 Γ2 Γ3 Γ23 : QCtx τ n} {A B C : τ}
    (s : Γ.Split Γ12 Γ3) (t : Γ12.Split Γ1 Γ2)
    (u : Γ.Split Γ1 Γ23) (v : Γ23.Split Γ2 Γ3)
    (f : M.Hom (packed Γ1) A) (g : M.Hom (packed Γ2) B) (h : M.Hom (packed Γ3) C) :
    M.compose (split M.toSeqData s)
      (M.compose (M.tensor (M.compose (split M.toSeqData t) (M.tensor f g)) h)
        (M.associator A B C)) =
      M.compose (split M.toSeqData u)
        (M.tensor f (M.compose (split M.toSeqData v) (M.tensor g h))) := by
  rw [← M.toSeqData.tensor_right_before]
  simp only [M.toSeqData.compose_assoc]
  rw [M.toSeqData.tensor_associator]
  rw [← M.toSeqData.compose_assoc (M.right (split M.toSeqData t) (packed Γ3)),
    ← M.toSeqData.compose_assoc, split_assoc M.toSeqData s t u v]
  simp only [M.toSeqData.compose_assoc]
  rw [M.toSeqData.tensor_left_before _ _ _ (split_pure M.toSeqData v)]

/-- Split a substitution tail and move its last computation to the left. -/
theorem split_tensor_left {e η : ε} {n : Nat}
    {Γ Γ12 Γ1 Γ2 Γ3 Γ13 : QCtx τ n} {A B C : τ}
    (s : Γ.Split Γ12 Γ3) (t : Γ12.Split Γ1 Γ2)
    (u : Γ.Split Γ13 Γ2) (v : Γ13.Split Γ1 Γ3)
    (f : M.Hom (packed Γ1) A) (g : M.Hom (packed Γ2) B) (h : M.Hom (packed Γ3) C)
    (hm : EffectSystem.commutes e η) (hg : M.hasEffect e g) (hh : M.hasEffect η h) :
    M.compose (split M.toSeqData s)
      (M.compose (M.tensor (M.compose (split M.toSeqData t) (M.tensor f g)) h)
        (M.compose (M.associator A B C)
          (M.compose (M.left A (M.braiding B C)) (M.associatorInv A C B)))) =
      M.compose (split M.toSeqData u)
        (M.tensor (M.compose (split M.toSeqData v) (M.tensor f h)) g) := by
  rw [← M.toSeqData.tensor_right_before]
  simp only [M.toSeqData.compose_assoc]
  rw [M.toSeqData.tensor_moveLeft f g h hm hg hh]
  have hs := congrArg (fun k => M.compose k (M.tensor (M.tensor f h) g))
    (split_swapAssoc M.toSeqData s t u v)
  simp only [M.toSeqData.compose_assoc] at hs
  rw [M.toSeqData.tensor_right_before] at hs
  exact hs

/-- Distributing a copied final computation through the two substitution outputs. -/
theorem split_tensor_both {e η : ε} {n : Nat}
    {Γ Γ12 Γ1 Γ2 Γ3 Γ13 Γ23 : QCtx τ n} {A B C : τ}
    (s : Γ.Split Γ12 Γ3) (t : Γ12.Split Γ1 Γ2)
    (u : Γ.Split Γ13 Γ23) (v : Γ13.Split Γ1 Γ3) (w : Γ23.Split Γ2 Γ3)
    (hc : Quantity.relevant ≤ quantity (packed Γ3))
    (hd : M.compose (split M.toSeqData s)
      (M.compose (M.tensor (split M.toSeqData t) (M.copy (packed Γ3) hc))
        (M.middleSwap (packed Γ1) (packed Γ2) (packed Γ3) (packed Γ3))) =
      M.compose (split M.toSeqData u) (M.tensor (split M.toSeqData v) (split M.toSeqData w)))
    (f : M.Hom (packed Γ1) A) (g : M.Hom (packed Γ2) B) (h : M.Hom (packed Γ3) C)
    (hm : EffectSystem.commutes e η) (hg : M.hasEffect e g) (hh : M.hasEffect η h) :
    M.compose (split M.toSeqData s)
      (M.compose (M.tensor (M.compose (split M.toSeqData t) (M.tensor f g))
        (M.compose (M.copy (packed Γ3) hc) (M.tensor h h))) (M.middleSwap A B C C)) =
      M.compose (split M.toSeqData u)
        (M.tensor (M.compose (split M.toSeqData v) (M.tensor f h))
          (M.compose (split M.toSeqData w) (M.tensor g h))) := by
  rw [← M.toSeqData.tensor_comp_pure _ _ _ _ (M.toSeqData.copy_pure _ hc)]
  simp only [M.toSeqData.compose_assoc]
  rw [M.toSeqData.tensor_middleSwap f g h h hm hg hh]
  have he := congrArg (fun k => M.compose k (M.tensor (M.tensor f h) (M.tensor g h))) hd
  simp only [M.toSeqData.compose_assoc] at he
  rw [M.toSeqData.tensor_comp_pure _ _ _ _ (split_pure M.toSeqData w)] at he
  exact he

/-- Pure maps to a pair of units are uniquely determined. -/
theorem pure_to_unitPair_unique {A : τ} (hA : Quantity.affine ≤ quantity A)
    (f g : M.Hom A (product Silmaril.unit Silmaril.unit))
    (hf : M.hasEffect ⊥ f) (hg : M.hasEffect ⊥ g) : f = g := by
  have h := (M.pure_to_unit_unique (M.compose f (M.leftUnitor Silmaril.unit))
    (M.toSeqData.compose_effect hf (M.toSeqData.leftUnitor_pure Silmaril.unit)) hA).trans
    (M.pure_to_unit_unique (M.compose g (M.leftUnitor Silmaril.unit))
      (M.toSeqData.compose_effect hg (M.toSeqData.leftUnitor_pure Silmaril.unit)) hA).symm
  have h' := congrArg (fun k => M.compose k (M.leftUnitorInv Silmaril.unit)) h
  simpa only [M.toSeqData.compose_assoc, M.toSeqData.leftUnitor_hom_inv,
    M.toSeqData.compose_identity] using h'

variable {F : Fragment} (K : ControlData M.toSeqData F) (E : ControlEffects K)

include E in
set_option backward.isDefEq.respectTransparency false in
/-- Destination splitting distributes an allowed native substitution, with its
actual categorical comparison and the original quantitative typing bounds. -/
theorem denoteSubstitution_split_ordered_exists (preserveLeft : Bool) (p : Polarity) {η : ε}
    {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n} {e : ε} {σ : Fin n → Term Φ m}
    (h : Substitution F Γ e σ Δ) (hh : h.EffectAllowed p η) :
    ∀ {Δl Δr : QCtx τ n} (s : Δ.Split Δl Δr),
      ∃ Γl Γr, ∃ ss : Γ.Split Γl Γr,
        ∃ hl : Substitution F Γl e σ Δl, ∃ hr : Substitution F Γr e σ Δr,
          hl.EffectAllowed p η ∧ hr.EffectAllowed p η ∧
          (if preserveLeft then Δl.linearity ≤ Γl.linearity else Δr.linearity ≤ Γr.linearity) ∧
          p.orient M.le
            (M.compose (denoteSubstitution M.toSeqData K h) (split M.toSeqData s))
            (M.compose (split M.toSeqData ss)
              (M.tensor (denoteSubstitution M.toSeqData K hl) (denoteSubstitution M.toSeqData K hr))) := by
  induction h with
  | @nil m Γ e hd =>
    intro Δl Δr s
    have hl : Δl = QCtx.nil := funext (fun i => Fin.elim0 i)
    have hr : Δr = QCtx.nil := funext (fun i => Fin.elim0 i)
    subst Δl
    subst Δr
    cases preserveLeft with
    | false =>
      refine ⟨Γ, Γ.zero, .zero_right Γ, .nil hd, .nil (QCtx.zero_discardable Γ),
        trivial, trivial, ?_, ?_⟩
      · rw [QCtx.zero_linearity]
        exact le_top
      · have he := pure_to_unitPair_unique M (discardable_quantity hd)
          (M.compose (discard M.toSeqData hd) (split M.toSeqData s))
          (M.compose (split M.toSeqData (QCtx.Split.zero_right Γ))
            (M.tensor (discard M.toSeqData hd) (discard M.toSeqData (QCtx.zero_discardable Γ))))
          (M.toSeqData.compose_effect (discard_pure _ _) (split_pure _ _))
          (M.toSeqData.compose_effect (split_pure _ _)
            (M.toSeqData.tensor_effect (discard_pure _ _) (discard_pure _ _)))
        change p.orient M.le _ _
        let := M.toSeqData.category
        let := M.toSeqData.homOrder
        cases p with
        | positive => exact he.le
        | negative => exact he.ge
    | true =>
      refine ⟨Γ.zero, Γ, .zero_left Γ, .nil (QCtx.zero_discardable Γ), .nil hd,
        trivial, trivial, ?_, ?_⟩
      · rw [QCtx.zero_linearity]
        exact le_top
      · have he := pure_to_unitPair_unique M (discardable_quantity hd)
          (M.compose (discard M.toSeqData hd) (split M.toSeqData s))
          (M.compose (split M.toSeqData (QCtx.Split.zero_left Γ))
            (M.tensor (discard M.toSeqData (QCtx.zero_discardable Γ)) (discard M.toSeqData hd)))
          (M.toSeqData.compose_effect (discard_pure _ _) (split_pure _ _))
          (M.toSeqData.compose_effect (split_pure _ _)
            (M.toSeqData.tensor_effect (discard_pure _ _) (discard_pure _ _)))
        change p.orient M.le _ _
        let := M.toSeqData.category
        let := M.toSeqData.homOrder
        cases p with
        | positive => exact he.le
        | negative => exact he.ge
  | @zero m n Γ Δ e σ h a A ih =>
    intro Δl Δr s
    obtain ⟨ΔL, ql, rfl⟩ := QCtx.exists_snoc_type Δl A (s 0).1
    obtain ⟨ΔR, qr, rfl⟩ := QCtx.exists_snoc_type Δr A (s 0).2.1
    have hhead : QCtx.SlotSplit A .zero ql qr := (s 0).2.2
    obtain ⟨Γl, Γr, ss, hl, hr, hhl, hhr, ht, he⟩ := ih hh (fun i => s i.succ)
    cases hhead with
    | left =>
      exact ⟨Γl, Γr, ss, .zero hl a A, .zero hr a A, hhl, hhr,
        by cases preserveLeft <;> simp only [Bool.false_eq_true, ↓reduceIte] at ht ⊢ <;> rw [QCtx.linearity_snoc] <;> exact inf_le_right.trans ht, he⟩
    | right =>
      exact ⟨Γl, Γr, ss, .zero hl a A, .zero hr a A, hhl, hhr,
        by cases preserveLeft <;> simp only [Bool.false_eq_true, ↓reduceIte] at ht ⊢ <;> rw [QCtx.linearity_snoc] <;> exact inf_le_right.trans ht, he⟩
    | both hc => exact False.elim hc
  | @cons m n Γ Γl Γr Δ e el er σ a A q s h ha hq hc hel her ih =>
    intro Δl Δr sd
    obtain ⟨ΔL, ql, rfl⟩ := QCtx.exists_snoc_type Δl A (sd 0).1
    obtain ⟨ΔR, qr, rfl⟩ := QCtx.exists_snoc_type Δr A (sd 0).2.1
    have hhead : QCtx.SlotSplit A (.used q) ql qr := (sd 0).2.2
    let st : Δ.Split ΔL ΔR := fun i => sd i.succ
    obtain ⟨ΓL, ΓR, ss, hl, hr, hhl, hhr, ht, he⟩ := ih hh.1 st
    have hlin (Δ0 : QCtx τ n) : (Δ0.snoc A (.used q)).linearity ≤ Γr.linearity := by
      rw [QCtx.linearity_snoc, Usage.linearity_used]
      exact (inf_le_left.trans inf_le_right).trans hq
    have haRefl : p.orient M.le (denote M.toSeqData K ha) (denote M.toSeqData K ha) := by
      cases p <;> exact M.toSeqData.le_refl _
    cases hhead with
    | left =>
      obtain ⟨ΓL', hp, hleft⟩ := s.swapAssoc ss
      refine ⟨ΓL', ΓR, hp, .cons hleft hl ha hq hc hel her,
        .zero (hr.effectMono hel) a A, ⟨hhl, hh.2⟩, hhr.effectMono hel,
        (by
          cases preserveLeft with
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; rw [QCtx.linearity_snoc]; exact inf_le_right.trans ht
          | true => exact hleft.le_linearity (by rw [QCtx.linearity_snoc]; exact inf_le_right.trans ht) (hlin ΔL)), ?_⟩
      have hstep := M.toSeqData.orient_compose_left p
        (M.toSeqData.orient_compose_right p (M.toSeqData.orient_tensor p he haRefl)
          (M.compose (M.associator (packed ΔL) (packed ΔR) A)
            (M.compose (M.left (packed ΔL) (M.braiding (packed ΔR) A))
              (M.associatorInv (packed ΔL) A (packed ΔR))))) (split M.toSeqData s)
      rw [split_tensor_left M s ss hp hleft _ _ _ hc
        (denoteSubstitution_effect M.toSeqData K E hr) (denote_effect K E ha)] at hstep
      change p.orient M.le
        (M.compose (M.compose (split M.toSeqData s)
          (M.tensor (denoteSubstitution M.toSeqData K h) (denote M.toSeqData K ha)))
          (M.compose (M.right (split M.toSeqData st) A)
            (M.compose (M.associator (packed ΔL) (packed ΔR) A)
              (M.compose (M.left (packed ΔL) (M.braiding (packed ΔR) A))
                (M.associatorInv (packed ΔL) A (packed ΔR)))))) _
      simp only [M.toSeqData.compose_assoc]
      rw [← M.toSeqData.compose_assoc (M.tensor _ _),
        M.toSeqData.tensor_right_after _ _ _ (split_pure M.toSeqData st)]
      simpa only [denoteSubstitution_zero, denoteSubstitution_effectMono, denoteSubstitution_cons,
        M.toSeqData.compose_assoc] using hstep
    | right =>
      obtain ⟨ΓR', hp, hright⟩ := s.swapAssoc ss.symm
      refine ⟨ΓL, ΓR', hp.symm, .zero (hl.effectMono hel) a A,
        .cons hright hr ha hq hc hel her, hhl.effectMono hel, ⟨hhr, hh.2⟩,
        (by
          cases preserveLeft with
          | false => exact hright.le_linearity (by rw [QCtx.linearity_snoc]; exact inf_le_right.trans ht) (hlin ΔR)
          | true => simp only [↓reduceIte]; rw [QCtx.linearity_snoc]; exact inf_le_right.trans ht), ?_⟩
      have hstep := M.toSeqData.orient_compose_left p
        (M.toSeqData.orient_compose_right p (M.toSeqData.orient_tensor p he haRefl)
          (M.associator (packed ΔL) (packed ΔR) A)) (split M.toSeqData s)
      rw [split_tensor_right M s ss hp.symm hright] at hstep
      change p.orient M.le
        (M.compose (M.compose (split M.toSeqData s)
          (M.tensor (denoteSubstitution M.toSeqData K h) (denote M.toSeqData K ha)))
          (M.compose (M.right (split M.toSeqData st) A)
            (M.associator (packed ΔL) (packed ΔR) A))) _
      rw [M.toSeqData.compose_assoc, M.toSeqData.tensor_split_right _ _ _ (split_pure M.toSeqData st)]
      simpa only [denoteSubstitution_zero, denoteSubstitution_effectMono, denoteSubstitution_cons] using hstep
    | both hcopy =>
      have hrel : Quantity.relevant ≤ Γr.linearity :=
        ((show Quantity.relevant ≤ q ⊓ quantity A from hcopy).trans inf_le_left).trans hq
      have hqa : Quantity.relevant ≤ q ⊓ quantity A := hcopy
      have hA : Quantity.relevant ≤ quantity A := hqa.trans inf_le_right
      have hcopyEff : EffectSystem.canCopy p er := (hqa.trans inf_le_left).trans hh.2.1
      obtain ⟨ΓL', ΓR', hp, hleft, hright, hdist⟩ := split_distribute M s ss hrel
      refine ⟨ΓL', ΓR', hp, .cons hleft hl ha hq hc hel her,
        .cons hright hr ha hq hc hel her, ⟨hhl, hh.2⟩, ⟨hhr, hh.2⟩,
        (by
          cases preserveLeft with
          | false => exact hright.le_linearity (by rw [QCtx.linearity_snoc]; exact inf_le_right.trans ht) (hlin ΔR)
          | true => exact hleft.le_linearity (by rw [QCtx.linearity_snoc]; exact inf_le_right.trans ht) (hlin ΔL)), ?_⟩
      have hstep := M.toSeqData.orient_compose_left p
        (M.toSeqData.orient_compose_right p
          (M.toSeqData.orient_tensor p he (M.toSeqData.copy_naturality p
            (denote M.toSeqData K ha) (hrel.trans (packed_quantity Γr)) hA hcopyEff
            (denote_effect K E ha))) (M.middleSwap (packed ΔL) (packed ΔR) A A)) (split M.toSeqData s)
      rw [split_tensor_both M s ss hp hleft hright _ hdist _ _ _ hc
        (denoteSubstitution_effect M.toSeqData K E hr) (denote_effect K E ha)] at hstep
      change p.orient M.le
        (M.compose (M.compose (split M.toSeqData s)
          (M.tensor (denoteSubstitution M.toSeqData K h) (denote M.toSeqData K ha)))
          (M.compose (M.tensor (split M.toSeqData st) (M.copy A hA))
            (M.middleSwap (packed ΔL) (packed ΔR) A A))) _
      rw [M.toSeqData.compose_assoc, ← M.toSeqData.compose_assoc (M.tensor _ _),
        M.toSeqData.tensor_comp_pure_middle _ _ _ _ (split_pure M.toSeqData st)]
      exact hstep

include E in
set_option backward.isDefEq.respectTransparency false in
/-- Destination splitting distributes an allowed native substitution, with its
actual categorical comparison and the original quantitative typing bounds. -/
theorem denoteSubstitution_split_exists (p : Polarity) {η : ε}
    {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n} {e : ε} {σ : Fin n → Term Φ m}
    (h : Substitution F Γ e σ Δ) (hh : h.EffectAllowed p η) :
    ∀ {Δl Δr : QCtx τ n} (s : Δ.Split Δl Δr),
      ∃ Γl Γr, ∃ ss : Γ.Split Γl Γr,
        ∃ hl : Substitution F Γl e σ Δl, ∃ hr : Substitution F Γr e σ Δr,
          hl.EffectAllowed p η ∧ hr.EffectAllowed p η ∧ Δl.linearity ≤ Γl.linearity ∧
          p.orient M.le
            (M.compose (denoteSubstitution M.toSeqData K h) (split M.toSeqData s))
            (M.compose (split M.toSeqData ss)
              (M.tensor (denoteSubstitution M.toSeqData K hl) (denoteSubstitution M.toSeqData K hr))) :=
  denoteSubstitution_split_ordered_exists M K E true p h hh

include E in
set_option backward.isDefEq.respectTransparency false in
/-- Destination splitting distributes an allowed native substitution, with its
actual categorical comparison and the original quantitative typing bounds. -/
theorem denoteSubstitution_split_right_exists (p : Polarity) {η : ε}
    {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n} {e : ε} {σ : Fin n → Term Φ m}
    (h : Substitution F Γ e σ Δ) (hh : h.EffectAllowed p η) :
    ∀ {Δl Δr : QCtx τ n} (s : Δ.Split Δl Δr),
      ∃ Γl Γr, ∃ ss : Γ.Split Γl Γr,
        ∃ hl : Substitution F Γl e σ Δl, ∃ hr : Substitution F Γr e σ Δr,
          hl.EffectAllowed p η ∧ hr.EffectAllowed p η ∧ Δr.linearity ≤ Γr.linearity ∧
          p.orient M.le
            (M.compose (denoteSubstitution M.toSeqData K h) (split M.toSeqData s))
            (M.compose (split M.toSeqData ss)
              (M.tensor (denoteSubstitution M.toSeqData K hl) (denoteSubstitution M.toSeqData K hr))) :=
  denoteSubstitution_split_ordered_exists M K E false p h hh

end Silmaril.Isotope.Refinement.Models.Denotation
