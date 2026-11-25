module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.TypingTransport
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.StructuralNaturality
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.VariableNaturality
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ControlEnvironment

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε)

theorem weaken_context_heq {n m : Nat} {Γ Γ' : QCtx τ n} {Δ Δ' : QCtx τ m}
    {ρ : Fin m → Fin n} (h : QCtx.Weakening Γ Δ ρ) (k : QCtx.Weakening Γ' Δ' ρ)
    (hs : Γ = Γ') (ht : Δ = Δ') :
    HEq (weaken M.toSeqData h) (weaken M.toSeqData k) := by
  cases hs
  cases ht
  rfl

theorem weaken_snoc {n : Nat} {Γ Δ : QCtx τ n} (A : τ)
    (h : QCtx.Weakening Γ Δ id) (k : QCtx.Weakening (Γ.snoc A) (Δ.snoc A) id) :
    weaken M.toSeqData k = M.toSeqData.right (weaken M.toSeqData h) A := by
  have he : id = Fin.cases 0 (fun i : Fin n => (id i).succ) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  exact congrArg Subtype.val (weakenPure_congr M.toSeqData k (.cons h le_rfl) he)

theorem weaken_restrict_snoc {n : Nat} {Γ : QCtx τ n} (A : τ) (p : Fin n → Bool)
    (h : QCtx.Weakening Γ (QCtx.restrict Γ p) id)
    (k : QCtx.Weakening (Γ.snoc A) (QCtx.restrict (Γ.snoc A) (Fin.cases true p)) id) :
    weaken M.toSeqData (Γ := Γ.snoc A) (Δ := QCtx.restrict (Γ.snoc A) (Fin.cases true p)) k =
      M.toSeqData.right (weaken M.toSeqData h) A := by
  have ht := QCtx.restrict_snoc_true Γ A (.used ⊤) p
  have k' : QCtx.Weakening (Γ.snoc A) ((QCtx.restrict Γ p).snoc A) id := ht ▸ k
  exact (eq_of_heq (weaken_context_heq M k k' rfl ht)).trans (weaken_snoc M A h k')

private theorem snocId {n : Nat} {Γ Δ : QCtx τ n}
    (h : QCtx.Weakening Γ Δ id) (A : τ) : QCtx.Weakening (Γ.snoc A) (Δ.snoc A) id := by
  have he : Fin.cases 0 (fun i : Fin n => (id i).succ) = id := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  exact he ▸ QCtx.Weakening.cons h le_rfl

theorem weaken_restrict_snoc₂ {n : Nat} {Γ : QCtx τ n} (A B : τ) (p : Fin n → Bool)
    (h : QCtx.Weakening Γ (QCtx.restrict Γ p) id)
    (k : QCtx.Weakening ((Γ.snoc A).snoc B)
      (QCtx.restrict ((Γ.snoc A).snoc B) (Fin.cases true (Fin.cases true p))) id) :
    weaken M.toSeqData (Γ := (Γ.snoc A).snoc B)
      (Δ := QCtx.restrict ((Γ.snoc A).snoc B) (Fin.cases true (Fin.cases true p))) k =
      M.toSeqData.right (M.toSeqData.right (weaken M.toSeqData h) A) B := by
  have ht : QCtx.restrict ((Γ.snoc A).snoc B) (Fin.cases true (Fin.cases true p)) =
      ((QCtx.restrict Γ p).snoc A).snoc B := by simp only [QCtx.restrict_snoc_true]
  have k' : QCtx.Weakening ((Γ.snoc A).snoc B) (((QCtx.restrict Γ p).snoc A).snoc B) id := ht ▸ k
  exact (eq_of_heq (weaken_context_heq M k k' rfl ht)).trans
    ((weaken_snoc M B (snocId h A) k').trans (congrArg (fun f => M.toSeqData.right f B)
      (weaken_snoc M A h (snocId h A))))

set_option backward.isDefEq.respectTransparency false in
/-- Strengthening away unused slots preserves categorical interpretation in every fragment. -/
theorem denote_restrict {F : Fragment} (K : ControlData M.toSeqData F) (N : ControlEnvironment K) {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t : Term Φ n} {A : τ} (h : HasType F Γ e t A)
    (p : Fin n → Bool) (hp : Term.Covered p t) :
    denote M.toSeqData K h = M.toSeqData.compose
      (weaken M.toSeqData (h.coveringWeakening p hp)) (denote M.toSeqData K (h.restrict p hp)) := by
  induction h with
  | @var n Γ e i hi =>
    have hv := weakenPure_variable M (HasType.coveringWeakening (HasType.var (ε := ε) (F := F) (e := e) i hi) p hp) i
      (hi.restrict p (hp i (by simp [Term.uses])))
    exact (congrArg Subtype.val (eq_of_heq hv)).symm
  | op hf ha ih =>
    change M.toSeqData.compose (denote M.toSeqData K ha) _ = _
    rw [ih p hp]
    exact M.toSeqData.compose_assoc _ _ _
  | unit hd =>
    exact (M.toSeqData.pure_discard_natural _ (weaken_pure _ _) _ _).symm
  | pair s ha hb iha ihb =>
    have pa : Term.Covered p _ := fun i hi => hp i (Bool.or_eq_true_iff.mpr (.inl hi))
    have pb : Term.Covered p _ := fun i hi => hp i (Bool.or_eq_true_iff.mpr (.inr hi))
    change M.toSeqData.compose (split M.toSeqData s)
      (M.toSeqData.tensor (denote M.toSeqData K ha) (denote M.toSeqData K hb)) = _
    rw [iha p pa, ihb p pb, ← M.toSeqData.tensor_comp_pure _ _ _ _ (weaken_pure _ _)]
    rw [← M.toSeqData.compose_assoc, ← weaken_split M _ s (s.restrict p)]
    exact M.toSeqData.compose_assoc _ _ _
  | @let₁ n Γ Γl Γr e a b A B s ha hb iha ihb =>
    have pa : Term.Covered p a := fun i hi => hp i (Bool.or_eq_true_iff.mpr (.inl hi))
    have pb : Term.Covered (Fin.cases true p) b := fun i => Fin.cases (fun _ => rfl)
      (fun j hj => hp j (Bool.or_eq_true_iff.mpr (.inr hj))) i
    have wl : QCtx.Weakening Γl (QCtx.restrict Γl p) id := by
      apply QCtx.weakening_restrict
      intro i hi
      apply hb.unused_discardable (i := i.succ)
      cases hu : Term.uses b i.succ
      · rfl
      · exact False.elim (Bool.noConfusion ((pb i.succ hu).symm.trans hi))
    change M.toSeqData.compose (split M.toSeqData s)
      (M.toSeqData.compose (M.toSeqData.left _ (denote M.toSeqData K ha)) (denote M.toSeqData K hb)) = _
    rw [iha p pa, ihb (Fin.cases true p) pb, weaken_restrict_snoc M A p wl]
    symm
    change M.toSeqData.compose (weaken M.toSeqData _)
      (M.toSeqData.compose (split M.toSeqData (s.restrict p))
        (M.toSeqData.compose (M.toSeqData.left _ (denote M.toSeqData K (ha.restrict p pa)))
          (denote M.toSeqData K ((hb.restrict (Fin.cases true p) pb).castContext (Δ := (QCtx.restrict Γl p).snoc A) (QCtx.restrict_snoc_true Γl A (.used ⊤) p))))) = _
    rw [denote_restrict_snoc_cast, ← M.toSeqData.compose_assoc,
      weaken_split M _ s (s.restrict p) wl (ha.coveringWeakening p pa)]
    simp only [M.toSeqData.compose_assoc]
    rw [← M.toSeqData.compose_assoc (M.toSeqData.tensor _ _) (M.toSeqData.left _ _),
      M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ _)]
    simp only [M.toSeqData.compose_assoc]
  | @let₂ n Γ Γl Γr e a b A B C s ha hb iha ihb =>
    have pa : Term.Covered p a := fun i hi => hp i (Bool.or_eq_true_iff.mpr (.inl hi))
    have pb : Term.Covered (Fin.cases true (Fin.cases true p)) b := fun i => Fin.cases (fun _ => rfl)
      (fun j => Fin.cases (fun _ => rfl)
        (fun k hk => hp k (Bool.or_eq_true_iff.mpr (.inr hk))) j) i
    have wl : QCtx.Weakening Γl (QCtx.restrict Γl p) id := by
      apply QCtx.weakening_restrict
      intro i hi
      apply hb.unused_discardable (i := i.succ.succ)
      cases hu : Term.uses b i.succ.succ
      · rfl
      · exact False.elim (Bool.noConfusion ((pb i.succ.succ hu).symm.trans hi))
    change M.toSeqData.compose (split M.toSeqData s)
      (M.toSeqData.compose (M.toSeqData.left _ (denote M.toSeqData K ha))
        (M.toSeqData.compose (M.toSeqData.associatorInv _ A B) (denote M.toSeqData K hb))) = _
    rw [iha p pa, ihb (Fin.cases true (Fin.cases true p)) pb, weaken_restrict_snoc₂ M A B p wl]
    symm
    change M.toSeqData.compose (weaken M.toSeqData _)
      (M.toSeqData.compose (split M.toSeqData (s.restrict p))
        (M.toSeqData.compose (M.toSeqData.left _ (denote M.toSeqData K (ha.restrict p pa)))
          (M.toSeqData.compose (M.toSeqData.associatorInv _ A B)
            (denote M.toSeqData K
              ((hb.restrict (Fin.cases true (Fin.cases true p)) pb).castContext
                (Δ := ((QCtx.restrict Γl p).snoc A).snoc B)
                (by simp only [QCtx.restrict_snoc_true])))))) = _
    rw [denote_castContext]
    change M.toSeqData.compose (weaken M.toSeqData _)
      (M.toSeqData.compose (split M.toSeqData (s.restrict p))
        (M.toSeqData.compose (M.toSeqData.left _ (denote M.toSeqData K (ha.restrict p pa)))
          (M.toSeqData.compose (M.toSeqData.associatorInv _ A B)
            (denote M.toSeqData K (hb.restrict (Fin.cases true (Fin.cases true p)) pb))))) = _
    rw [← M.toSeqData.compose_assoc, weaken_split M _ s (s.restrict p) wl (ha.coveringWeakening p pa)]
    simp only [M.toSeqData.compose_assoc]
    rw [← M.toSeqData.compose_assoc (M.toSeqData.tensor _ _) (M.toSeqData.left _ _),
      M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ _)]
    simp only [M.toSeqData.compose_assoc]
    rw [← M.toSeqData.compose_assoc (M.toSeqData.right _ _) (M.toSeqData.associatorInv _ A B),
      M.toSeqData.associatorInv_natural_left]
    simp only [M.toSeqData.compose_assoc]
  | inl hg ha ih =>
    change M.toSeqData.compose (denote M.toSeqData K ha) _ = _
    rw [ih p hp]
    exact M.toSeqData.compose_assoc _ _ _
  | inr hg ha ih =>
    change M.toSeqData.compose (denote M.toSeqData K ha) _ = _
    rw [ih p hp]
    exact M.toSeqData.compose_assoc _ _ _
  | abort hg ha ih =>
    change M.toSeqData.compose (denote M.toSeqData K ha) _ = _
    rw [ih p hp]
    exact M.toSeqData.compose_assoc _ _ _
  | @case n Γ Γl Γr e a l r A B C hg s ha hl hr iha ihl ihr =>
    have pa : Term.Covered p a := fun i hi => hp i (Bool.or_eq_true_iff.mpr (.inl hi))
    have pl : Term.Covered (Fin.cases true p) l := fun i => Fin.cases (fun _ => rfl)
      (fun j hj => hp j (Bool.or_eq_true_iff.mpr (.inr (Bool.or_eq_true_iff.mpr (.inl hj))))) i
    have pr : Term.Covered (Fin.cases true p) r := fun i => Fin.cases (fun _ => rfl)
      (fun j hj => hp j (Bool.or_eq_true_iff.mpr (.inr (Bool.or_eq_true_iff.mpr (.inr hj))))) i
    have wl : QCtx.Weakening Γl (QCtx.restrict Γl p) id := by
      apply QCtx.weakening_restrict
      intro i hi
      apply hl.unused_discardable (i := i.succ)
      cases hu : Term.uses l i.succ
      · rfl
      · exact False.elim (Bool.noConfusion ((pl i.succ hu).symm.trans hi))
    change M.toSeqData.compose (split M.toSeqData s)
      (M.toSeqData.compose (M.toSeqData.left _ (denote M.toSeqData K ha))
        (M.toSeqData.compose (K.distribute hg _ A B)
          (K.desc hg (denote M.toSeqData K hl) (denote M.toSeqData K hr)))) = _
    rw [iha p pa, ihl (Fin.cases true p) pl, ihr (Fin.cases true p) pr,
      weaken_restrict_snoc M A p wl, weaken_restrict_snoc M B p wl]
    symm
    change M.toSeqData.compose (weaken M.toSeqData _)
      (M.toSeqData.compose (split M.toSeqData (s.restrict p))
        (M.toSeqData.compose (M.toSeqData.left _ (denote M.toSeqData K (ha.restrict p pa)))
          (M.toSeqData.compose (K.distribute hg _ A B)
            (K.desc hg
              (denote M.toSeqData K ((hl.restrict (Fin.cases true p) pl).castContext
                (Δ := (QCtx.restrict Γl p).snoc A) (QCtx.restrict_snoc_true Γl A (.used ⊤) p)))
              (denote M.toSeqData K ((hr.restrict (Fin.cases true p) pr).castContext
                (Δ := (QCtx.restrict Γl p).snoc B) (QCtx.restrict_snoc_true Γl B (.used ⊤) p))))))) = _
    rw [denote_restrict_snoc_cast, denote_restrict_snoc_cast,
      ← M.toSeqData.compose_assoc, weaken_split M _ s (s.restrict p) wl (ha.coveringWeakening p pa)]
    simp only [M.toSeqData.compose_assoc]
    rw [← M.toSeqData.compose_assoc (M.toSeqData.tensor _ _) (M.toSeqData.left _ _),
      M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ _)]
    simp only [M.toSeqData.compose_assoc]
    rw [N.case_natural]
  | @iter n Γ Γl Γr e a b A B hg s hu hi ha hb iha ihb =>
    have pa : Term.Covered p a := fun i hi => hp i (Bool.or_eq_true_iff.mpr (.inl hi))
    have pb : Term.Covered (Fin.cases true p) b := fun i => Fin.cases (fun _ => rfl)
      (fun j hj => hp j (Bool.or_eq_true_iff.mpr (.inr hj))) i
    have wl : QCtx.Weakening Γl (QCtx.restrict Γl p) id := by
      apply QCtx.weakening_restrict
      intro i hi
      apply hb.unused_discardable (i := i.succ)
      cases hv : Term.uses b i.succ
      · rfl
      · exact False.elim (Bool.noConfusion ((pb i.succ hv).symm.trans hi))
    have hD : (⊤ : Quantity) ≤ quantity (packed Γl) := hu ▸ packed_quantity Γl
    have hE : (⊤ : Quantity) ≤ quantity (packed (QCtx.restrict Γl p)) :=
      (QCtx.restrict_unrestricted hu p) ▸ packed_quantity (QCtx.restrict Γl p)
    change M.toSeqData.compose (split M.toSeqData s)
      (M.toSeqData.compose (M.toSeqData.left _ (denote M.toSeqData K ha))
        (K.iterateWithContext hg _ (le_trans le_top hD) (le_trans le_top hD) (denote M.toSeqData K hb))) = _
    rw [iha p pa, ihb (Fin.cases true p) pb, weaken_restrict_snoc M A p wl]
    symm
    change M.toSeqData.compose (weaken M.toSeqData _)
      (M.toSeqData.compose (split M.toSeqData (s.restrict p))
        (M.toSeqData.compose (M.toSeqData.left _ (denote M.toSeqData K (ha.restrict p pa)))
          (K.iterateWithContext hg _ (le_trans le_top hE) (le_trans le_top hE)
            (denote M.toSeqData K ((hb.restrict (Fin.cases true p) pb).castContext
              (Δ := (QCtx.restrict Γl p).snoc A) (QCtx.restrict_snoc_true Γl A (.used ⊤) p)))))) = _
    rw [denote_restrict_snoc_cast, ← M.toSeqData.compose_assoc,
      weaken_split M _ s (s.restrict p) wl (ha.coveringWeakening p pa)]
    simp only [M.toSeqData.compose_assoc]
    rw [← M.toSeqData.compose_assoc (M.toSeqData.tensor _ _) (M.toSeqData.left _ _),
      M.toSeqData.tensor_left_pure _ _ _ (weaken_pure _ _)]
    simp only [M.toSeqData.compose_assoc]
    rw [N.iter_natural hg _ (weaken_pure _ _) (le_trans le_top hD) (le_trans le_top hD)]

/-- Restriction can be reindexed to any equal chosen target context. -/
theorem denote_restrict_to {F : Fragment} (K : ControlData M.toSeqData F) (N : ControlEnvironment K)
    {n : Nat} {Γ Δ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ} (h : HasType F Γ e t A)
    (p : Fin n → Bool) (hp : Term.Covered p t) (he : QCtx.restrict Γ p = Δ)
    (w : QCtx.Weakening Γ Δ id) :
    denote M.toSeqData K h = M.toSeqData.compose (weaken M.toSeqData w)
      (denote M.toSeqData K ((h.restrict p hp).castContext he)) := by
  cases he
  exact denote_restrict M K N h p hp

/-- Sequential specialization of the shared resource-restriction theorem. -/
theorem denoteSeq_restrict {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t : Term Φ n} {A : τ} (h : HasType .seq Γ e t A)
    (p : Fin n → Bool) (hp : Term.Covered p t) :
    denoteSeq M h = M.toSeqData.compose
      (weaken M.toSeqData (h.coveringWeakening p hp)) (denoteSeq M (h.restrict p hp)) :=
  denote_restrict M (ControlData.seq M) (ControlEnvironment.seq M) h p hp

/-- Restriction with its result context identified with any chosen representative. -/
theorem denoteSeq_restrict_to {n : Nat} {Γ Δ : QCtx τ n} {e : ε}
    {t : Term Φ n} {A : τ} (h : HasType .seq Γ e t A)
    (p : Fin n → Bool) (hp : Term.Covered p t) (he : QCtx.restrict Γ p = Δ)
    (w : QCtx.Weakening Γ Δ id) :
    denoteSeq M h = M.toSeqData.compose (weaken M.toSeqData w)
      (denoteSeq M ((h.restrict p hp).castContext he)) := by
  cases he
  exact denoteSeq_restrict M h p hp

/-- Branching specialization, derived from the actual distributive model laws. -/
theorem denoteCase_restrict (M : CaseModel.{u,v,w,r} τ Φ ε) {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t : Term Φ n} {A : τ} (h : HasType .case Γ e t A)
    (p : Fin n → Bool) (hp : Term.Covered p t) :
    denoteCase M h = M.toSeqData.compose
      (weaken M.toSeqData (h.coveringWeakening p hp)) (denoteCase M (h.restrict p hp)) :=
  denote_restrict M.toSeqModel (ControlData.case M) (ControlEnvironment.case M) h p hp

/-- Iterative specialization, using pure uniformity for retained environments. -/
theorem denoteIter_restrict (M : IterModel.{u,v,w,r} τ Φ ε) {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t : Term Φ n} {A : τ} (h : HasType .iter Γ e t A)
    (p : Fin n → Bool) (hp : Term.Covered p t) :
    denoteIter M h = M.toSeqData.compose
      (weaken M.toSeqData (h.coveringWeakening p hp)) (denoteIter M (h.restrict p hp)) :=
  denote_restrict M.toSeqModel (ControlData.iter M) (ControlEnvironment.iter M) h p hp

end Silmaril.Isotope.Refinement.Models.Denotation
