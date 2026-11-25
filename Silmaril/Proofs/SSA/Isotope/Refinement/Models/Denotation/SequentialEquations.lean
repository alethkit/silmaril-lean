module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Binding
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.OrderedInterpretation
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.WitnessCoherence

/-! # Structural equations shared by every control fragment -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation

universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F) (N : ControlEnvironment K) (H : WitnessCoherent M K)

namespace Sequential
include N H

/-- An inserted zero-use ambient binder contributes no semantic component. -/
theorem denote_underBinder_zero {n : Nat} {Γ : QCtx τ n} {e e' : ε}
    {t : Term Φ (n + 1)} {A B C : τ}
    (h : HasType F (Γ.snoc B) e t C)
    (k : HasType F ((Γ.snoc A .zero).snoc B) e' t.underBinder C) :
    denote M.toSeqData K k = denote M.toSeqData K h := by
  let w := (QCtx.Weakening.insertZero Γ A).up (A := B)
  have hw : weaken M.toSeqData w = M.identity (product (packed Γ) B) := by
    change M.right (weaken M.toSeqData (QCtx.Weakening.insertZero Γ A)) B = _
    have hz : weaken M.toSeqData (QCtx.Weakening.insertZero Γ A) =
        M.identity (packed Γ) := by
      have he := congrArg Subtype.val (weakenPure_skip M (QCtx.Weakening.refl Γ)
        (A := A) (q := .zero) le_rfl)
      exact he.trans (weaken_refl M.toSeqData Γ)
    rw [hz]
    exact M.toSeqData.right_identity _ _
  exact (denote_rename_of_typing M K N H h _ w k).trans
    (by rw [hw]; exact M.toSeqData.identity_compose _)

/-- Zero-use insertion below two bound components is also semantically inert. -/
theorem denote_underTwoBinders_zero {n : Nat} {Γ : QCtx τ n} {e e' : ε}
    {t : Term Φ (n + 2)} {A B C D : τ}
    (h : HasType F ((Γ.snoc B).snoc C) e t D)
    (k : HasType F (((Γ.snoc A .zero).snoc B).snoc C) e' t.underTwoBinders D) :
    denote M.toSeqData K k = denote M.toSeqData K h := by
  let w := QCtx.Weakening.insertZeroUnderTwo Γ A B C
  have hw : weaken M.toSeqData w = M.identity (product (product (packed Γ) B) C) := by
    have he : weaken M.toSeqData w =
        weaken M.toSeqData (((QCtx.Weakening.insertZero Γ A).up B).up C) := by
      apply congrArg Subtype.val
      apply weakenPure_congr
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact Fin.cases rfl (fun _ => rfl) j
    rw [he]
    change M.right (M.right (weaken M.toSeqData (QCtx.Weakening.insertZero Γ A)) B) C = _
    have hz : weaken M.toSeqData (QCtx.Weakening.insertZero Γ A) = M.identity (packed Γ) := by
      exact (congrArg Subtype.val (weakenPure_skip M (QCtx.Weakening.refl Γ)
        (A := A) (q := .zero) le_rfl)).trans (weaken_refl M.toSeqData Γ)
    rw [hz]
    exact (congrArg (fun f => M.right f C) (M.toSeqData.right_identity (packed Γ) B)).trans
      (M.toSeqData.right_identity _ _)
  exact (denote_rename_of_typing M K N H h _ w k).trans
    (by rw [hw]; exact M.toSeqData.identity_compose _)

set_option backward.isDefEq.respectTransparency false in
/-- Pair elimination factors through ordinary binding of its scrutinee. -/
theorem denote_pairBind {n : Nat} {Γ Γl Γr : QCtx τ n}
    {e eL eR : ε} {a : Term Φ n} {c : Term Φ (n + 2)} {A B C : τ}
    (s : Γ.Split Γl Γr) (ha : HasType F Γr e a (product A B))
    (hc : HasType F ((Γl.snoc A).snoc B) e c C)
    (hl : HasType F Γ eL (.let₂ a c) C)
    (hr : HasType F Γ eR (.let₁ a (.let₂ (.bv 0) c.underTwoBinders)) C) :
    denote M.toSeqData K hl = denote M.toSeqData K hr := by
  let hv : HasType F (Γl.zero.snoc (product A B)) e (.bv 0 : Term Φ (n + 1)) (product A B) :=
    .var 0 (QCtx.varAllowed_snoc (QCtx.zero_discardable Γl) (product A B))
  let kc := hc.rename _ (QCtx.Weakening.insertZeroUnderTwo Γl (product A B) A B)
  let si := (QCtx.Split.zero_right Γl).snoc (.right (.used ⊤)) (A := product A B)
  let ki := HasType.let₂ si hv kc
  have hi : denote M.toSeqData K ki = M.compose (M.associatorInv (packed Γl) A B) (denote M.toSeqData K hc) := by
    change M.compose (split M.toSeqData si)
      (M.compose (M.left (packed Γl) (denote M.toSeqData K hv))
        (M.compose (M.associatorInv (packed Γl) A B) (denote M.toSeqData K kc))) = _
    rw [denote_underTwoBinders_zero M K N H hc kc]
    rw [← M.toSeqData.compose_assoc]
    change M.compose
      (M.compose (split M.toSeqData si) (M.left (packed Γl)
        (M.compose (M.right (discard M.toSeqData (QCtx.zero_discardable Γl)) (product A B))
          (M.leftUnitor (product A B)))))
      (M.compose (M.associatorInv (packed Γl) A B) (denote M.toSeqData K hc)) = _
    rw [newest_split_variable M Γl (product A B) (QCtx.zero_discardable Γl)]
    exact M.toSeqData.identity_compose _
  calc
    denote M.toSeqData K hl = denote M.toSeqData K (.let₂ s ha hc) := H _ _
    _ = denote M.toSeqData K (.let₁ s ha ki) := by
      change M.compose (split M.toSeqData s)
          (M.compose (M.left (packed Γl) (denote M.toSeqData K ha))
            (M.compose (M.associatorInv (packed Γl) A B) (denote M.toSeqData K hc))) =
        M.compose (split M.toSeqData s)
          (M.compose (M.left (packed Γl) (denote M.toSeqData K ha)) (denote M.toSeqData K ki))
      rw [hi]
    _ = denote M.toSeqData K hr := H _ _

set_option backward.isDefEq.respectTransparency false in
/-- Binding an instruction result agrees with first binding its argument. -/
theorem denote_letOp {n : Nat} {Γ Γl Γr : QCtx τ n}
    {e eL eR : ε} {a : Term Φ n} {c : Term Φ (n + 1)} {f : Φ} {C : τ}
    (s : Γ.Split Γl Γr) (hf : instrEff f ≤ e)
    (ha : HasType F Γr e a (instrSrc f))
    (hc : HasType F (Γl.snoc (instrTrg f)) e c C)
    (hl : HasType F Γ eL (.let₁ (.op f a) c) C)
    (hr : HasType F Γ eR (.let₁ a (.let₁ (.op f (.bv 0)) c.underBinder)) C) :
    denote M.toSeqData K hl = denote M.toSeqData K hr := by
  let hv : HasType F (Γl.zero.snoc (instrSrc f)) e (.bv 0 : Term Φ (n + 1)) (instrSrc f) :=
    .var 0 (QCtx.varAllowed_snoc (QCtx.zero_discardable Γl) (instrSrc f))
  let w := (QCtx.Weakening.insertZero Γl (instrSrc f)).up (instrTrg f)
  let kc : HasType F ((Γl.snoc (instrSrc f) .zero).snoc (instrTrg f)) e c.underBinder C :=
    hc.rename _ w
  let si := (QCtx.Split.zero_right Γl).snoc (.right (.used ⊤)) (A := instrSrc f)
  let ki := HasType.let₁ si (.op hf hv) kc
  have hi : denote M.toSeqData K ki = M.compose (M.left (packed Γl) (M.instruction f)) (denote M.toSeqData K hc) := by
    change M.compose (split M.toSeqData si)
        (M.compose (M.left (packed Γl) (M.compose (denote M.toSeqData K hv) (M.instruction f)))
          (denote M.toSeqData K kc)) = _
    rw [denote_underBinder_zero M K N H hc kc]
    change M.compose (split M.toSeqData si)
        (M.compose (M.left (packed Γl)
          (M.compose (M.compose (M.right (discard M.toSeqData (QCtx.zero_discardable Γl)) (instrSrc f))
            (M.leftUnitor (instrSrc f))) (M.instruction f))) (denote M.toSeqData K hc)) = _
    rw [M.toSeqData.compose_assoc, ← M.toSeqData.compose_assoc]
    rw [newest_split_bind M Γl (QCtx.zero_discardable Γl) (M.instruction f)]
  calc
    denote M.toSeqData K hl = denote M.toSeqData K (.let₁ s (.op hf ha) hc) := H _ _
    _ = denote M.toSeqData K (.let₁ s ha ki) := by
      change M.compose (split M.toSeqData s)
          (M.compose (M.left (packed Γl) (M.compose (denote M.toSeqData K ha) (M.instruction f)))
            (denote M.toSeqData K hc)) =
        M.compose (split M.toSeqData s)
          (M.compose (M.left (packed Γl) (denote M.toSeqData K ha)) (denote M.toSeqData K ki))
      rw [hi, M.toSeqData.left_compose, M.toSeqData.compose_assoc]
    _ = denote M.toSeqData K hr := H _ _

set_option backward.isDefEq.respectTransparency false in
/-- Nested ordinary binding is associative, including the quantitative
reassociation of its three ambient resource groups. -/
theorem denote_letLet {n : Nat} {Γ Γl Γm Γr Γc : QCtx τ n}
    {e eL eR : ε} {a : Term Φ n} {b c : Term Φ (n + 1)} {A B C : τ}
    (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γm)
    (ha : HasType F Γr e a A) (hb : HasType F (Γm.snoc A) e b B)
    (hc : HasType F (Γl.snoc B) e c C)
    (hl : HasType F Γ eL (.let₁ (.let₁ a b) c) C)
    (hr : HasType F Γ eR (.let₁ a (.let₁ b c.underBinder)) C) :
    denote M.toSeqData K hl = denote M.toSeqData K hr := by
  obtain ⟨Γmr, u, v⟩ := outer.swapAssoc inner.symm
  let kc : HasType F ((Γl.snoc A .zero).snoc B) e c.underBinder C :=
    hc.rename _ ((QCtx.Weakening.insertZero Γl A).up B)
  let ki := HasType.let₁ (inner.snoc (.right (.used ⊤)) (A := A)) hb kc
  have hi : denote M.toSeqData K ki = M.compose (M.right (split M.toSeqData inner) A)
      (M.compose (M.associator (packed Γl) (packed Γm) A)
        (M.compose (M.left (packed Γl) (denote M.toSeqData K hb)) (denote M.toSeqData K hc))) := by
    change M.compose (M.compose (M.right (split M.toSeqData inner) A)
        (M.associator (packed Γl) (packed Γm) A))
      (M.compose (M.left (packed Γl) (denote M.toSeqData K hb)) (denote M.toSeqData K kc)) = _
    rw [denote_underBinder_zero M K N H hc kc, M.toSeqData.compose_assoc]
  calc
    denote M.toSeqData K hl = denote M.toSeqData K (.let₁ u.symm (.let₁ v ha hb) hc) := H _ _
    _ = denote M.toSeqData K (.let₁ outer ha ki) := by
      change M.compose (split M.toSeqData u.symm)
          (M.compose (M.left (packed Γl) (M.compose (split M.toSeqData v)
            (M.compose (M.left (packed Γm) (denote M.toSeqData K ha)) (denote M.toSeqData K hb))))
            (denote M.toSeqData K hc)) =
        M.compose (split M.toSeqData outer)
          (M.compose (M.left (packed Γc) (denote M.toSeqData K ha)) (denote M.toSeqData K ki))
      rw [hi, ← M.toSeqData.compose_assoc, split_bind_assoc M outer inner u.symm v]
      simp only [M.toSeqData.compose_assoc]
    _ = denote M.toSeqData K hr := H _ _

omit N in
/-- Returning a just-bound value is the identity continuation, independently
of the particular endpoint typing witnesses. -/
theorem denote_let_return {n : Nat} {Γ : QCtx τ n} {e e' : ε}
    {a : Term Φ n} {A : τ} (ha : HasType F Γ e a A)
    (hl : HasType F Γ e' (.let₁ a (.bv 0)) A) :
    denote M.toSeqData K hl = denote M.toSeqData K ha := by
  let hv : HasType F (Γ.zero.snoc A) e (.bv 0 : Term Φ (n + 1)) A :=
    .var 0 (QCtx.varAllowed_snoc (QCtx.zero_discardable Γ) A)
  exact (H hl (.let₁ (QCtx.Split.zero_left Γ) ha hv)).trans
    (Denotation.denote_let_return M K ha)

omit N in
/-- The unit eta scheme preserves the effectful computation producing unit. -/
theorem denote_term {n : Nat} {Γ : QCtx τ n} {e e' : ε}
    {a : Term Φ n} (ha : HasType F Γ e a Silmaril.unit)
    (hl : HasType F Γ e' (.let₁ a .unit) Silmaril.unit) :
    denote M.toSeqData K hl = denote M.toSeqData K ha := by
  have hd : (Γ.zero.snoc (Silmaril.unit : τ)).Discardable := by
    intro i
    cases i using Fin.cases with
    | zero =>
      change Usage.zero ≤ Usage.effective (.used ⊤) (quantity (Silmaril.unit : τ))
      rw [TypeQuantity.unit_quantity, Usage.effective_used]
      decide
    | succ i => exact le_rfl
  let hu : HasType F (Γ.zero.snoc Silmaril.unit) e (.unit : Term Φ (n + 1)) Silmaril.unit := .unit hd
  let hv : HasType F (Γ.zero.snoc Silmaril.unit) e (.bv 0 : Term Φ (n + 1)) Silmaril.unit :=
    .var 0 (QCtx.varAllowed_snoc (QCtx.zero_discardable Γ) Silmaril.unit)
  have hu_pure : M.hasEffect ⊥ (denote M.toSeqData K hu) := discard_pure _ hd
  have hv_pure : M.hasEffect ⊥ (denote M.toSeqData K hv) := variable_pure _ _ _
  have he : denote M.toSeqData K hu = denote M.toSeqData K hv :=
    (M.pure_to_unit_unique _ hu_pure (discardable_quantity hd)).trans
      (M.pure_to_unit_unique _ hv_pure (discardable_quantity hd)).symm
  calc
    denote M.toSeqData K hl = denote M.toSeqData K (.let₁ (QCtx.Split.zero_left Γ) ha hu) :=
      H _ _
    _ = denote M.toSeqData K (.let₁ (QCtx.Split.zero_left Γ) ha hv) := by
      change M.compose (split M.toSeqData (QCtx.Split.zero_left Γ))
          (M.compose (M.left (packed Γ.zero) (denote M.toSeqData K ha)) (denote M.toSeqData K hu)) =
        M.compose (split M.toSeqData (QCtx.Split.zero_left Γ))
          (M.compose (M.left (packed Γ.zero) (denote M.toSeqData K ha)) (denote M.toSeqData K hv))
      rw [he]
    _ = denote M.toSeqData K ha := Denotation.denote_let_return M K ha

end Sequential
end Silmaril.Isotope.Refinement.Models.Denotation
