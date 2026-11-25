module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.CaseSoundness
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationSimulation

/-! # Canonical equations for contextual iteration -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : CaseData.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (it : F.HasIter → ∀ {A B : τ}, M.Hom A (coprod B A) → M.Hom A B)
local notation "K" => ControlData.ofCase M F it

set_option backward.isDefEq.respectTransparency false in
/-- Iterating the newest parameter realizes the contextual loop directly. -/
theorem denote_iterParameter_exists (N : ControlEnvironment K)
    {n : Nat} {Γ : QCtx τ n} {e : ε} {b : Term Φ (n+1)} {A B : τ}
    (cap : F.HasIter) (hu : Γ.linearity = ⊤) (hi : EffectSystem.iterable e)
    (hb : HasType F (Γ.snoc A) e b (coprod B A))
    (c : Quantity.relevant ≤ quantity (packed Γ)) (d : Quantity.affine ≤ quantity (packed Γ)) :
    ∃ k : HasType F (Γ.snoc A) e (.iter (.bv 0) b.underBinder) B,
      denote M.toSeqData K k = (K).iterateWithContext cap (packed Γ) c d (denote M.toSeqData K hb) := by
  obtain ⟨kb, hkb⟩ := denote_underBinder_zero_exists M it N (A := A) hb
  let hv : HasType F (Γ.zero.snoc A) e (.bv 0 : Term Φ (n+1)) A :=
    .var 0 (QCtx.varAllowed_snoc (QCtx.zero_discardable Γ) A)
  let si := (QCtx.Split.zero_right Γ).snoc (.right (.used ⊤)) (A := A)
  have hui : (Γ.snoc A .zero).linearity = ⊤ := by
    simp only [QCtx.linearity_snoc, Usage.linearity_zero, hu, inf_top_eq]
    rfl
  let ki := HasType.iter cap si hui hi hv kb
  refine ⟨ki, ?_⟩
  change M.compose (split M.toSeqData si)
    (M.compose (M.left (packed Γ) (denote M.toSeqData K hv))
      ((K).iterateWithContext cap (packed Γ) c d (denote M.toSeqData K kb))) = _
  rw [hkb, ← M.compose_assoc]
  change M.compose (M.compose (split M.toSeqData si)
    (M.left (packed Γ) (M.compose (M.right (discard M.toSeqData (QCtx.zero_discardable Γ)) A)
      (M.leftUnitor A)))) _ = _
  rw [newest_split_variable M.toSeqModel Γ A (QCtx.zero_discardable Γ)]
  exact M.identity_compose _

set_option backward.isDefEq.respectTransparency false in
/-- The iteration binder factors through ordinary binding without changing
its explicit state machine or the effectful initial computation. -/
theorem denote_iterBind_exists (N : ControlEnvironment K)
    {n : Nat} {Γ Γl Γr : QCtx τ n} {e : ε}
    {a : Term Φ n} {b : Term Φ (n+1)} {A B : τ}
    (cap : F.HasIter) (s : Γ.Split Γl Γr) (hu : Γl.linearity = ⊤)
    (hi : EffectSystem.iterable e)
    (ha : HasType F Γr e a A) (hb : HasType F (Γl.snoc A) e b (coprod B A)) :
    ∃ k : HasType F Γ e (.let₁ a (.iter (.bv 0) b.underBinder)) B,
      denote M.toSeqData K (.iter cap s hu hi ha hb) = denote M.toSeqData K k := by
  have ht : (⊤ : Quantity) ≤ quantity (packed Γl) := hu ▸ packed_quantity Γl
  obtain ⟨ki, hki⟩ := denote_iterParameter_exists M it N cap hu hi hb (le_top.trans ht) (le_top.trans ht)
  refine ⟨.let₁ s ha ki, ?_⟩
  change M.compose (split M.toSeqData s) (M.compose (M.left _ (denote M.toSeqData K ha)) _) =
    M.compose (split M.toSeqData s) (M.compose (M.left _ (denote M.toSeqData K ha)) (denote M.toSeqData K ki))
  rw [hki]
  rfl

end Silmaril.Isotope.Refinement.Models.Denotation
