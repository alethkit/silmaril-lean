module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionRenaming

/-! # Semantic identity for admissible quantitative substitutions

The literal native substitution judgment need not admit identity at every
annotation. Normalization followed by target weakening does, and its
categorical composite is the identity arrow.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F) (N : ControlEnvironment K)

include N in
/-- Lifting an allowed substitution through any used binder right-whiskers its action.
The fresh variable is pure and its annotation is normalized by meeting it with the type quantity. -/
theorem denoteSubstitution_upUsed_exists (p : Polarity) {η : ε}
    {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n} {e : ε} {σ : Fin n → Term Φ m}
    (h : Substitution F Γ e σ Δ) (hh : h.EffectAllowed p η) (A : τ) (q : Quantity) :
    ∃ h' : Substitution F (Γ.snoc A (.used q)) e (Tm.upSub σ) (Δ.snoc A (.used (q ⊓ quantity A))),
      h'.EffectAllowed p η ∧
      denoteSubstitution M.toSeqData K h' = M.right (denoteSubstitution M.toSeqData K h) A := by
  obtain ⟨hl, hlg, hle⟩ := denoteSubstitution_rename_exists M K N p h hh Fin.succ
    (QCtx.Weakening.insertZero Γ A)
  have hva : (Γ.zero.snoc A (.used q)).VarAllowed 0 := by
    constructor
    · change Quantity.linear ⊓ quantity A ≤ q ⊓ quantity A
      exact inf_le_inf bot_le le_rfl
    · intro i hi
      cases i using Fin.cases with
      | zero => exact False.elim (hi rfl)
      | succ j => exact le_rfl
  let hv := HasType.var (F := F) (Φ := Φ) (e := (⊥ : ε)) 0
    hva
  have hq : q ⊓ quantity A ≤ (Γ.zero.snoc A (.used q)).linearity := by
    simp only [QCtx.linearity_snoc, QCtx.zero_linearity, Usage.linearity_used,
      inf_top_eq]
    exact (inf_comm q (quantity A)).le
  let ss := (QCtx.Split.zero_right Γ).snoc (.right (.used q)) (A := A)
  let hu : Substitution F (Γ.snoc A (.used q)) e (Tm.upSub σ) (Δ.snoc A (.used (q ⊓ quantity A))) :=
    .cons ss hl hv hq (EffectSystem.pure_commutes e).symm le_rfl bot_le
  refine ⟨hu, ⟨hlg, ?_, EffectSystem.pure_moves p η⟩, ?_⟩
  · rw [EffectSystem.quantity_pure]
    exact le_top
  · change M.compose (B := product (packed Γ) (product (packed Γ.zero) A))
      (split M.toSeqData ss)
      (M.tensor (A := packed Γ) (D := product (packed Γ.zero) A)
        (denoteSubstitution M.toSeqData K (Γ := Γ.snoc A .zero) hl)
        (denote M.toSeqData K (Γ := Γ.zero.snoc A (.used q)) hv)) = _
    have hle' : denoteSubstitution M.toSeqData K hl = denoteSubstitution M.toSeqData K h := by
      simpa only [packed_snoc_zero, weaken_insertZero, M.toSeqData.identity_compose] using hle
    rw [hle']
    change M.compose (B := product (packed Γ) (product (packed Γ.zero) A))
      (split M.toSeqData ss)
      (M.tensor (A := packed Γ) (D := product (packed Γ.zero) A) (denoteSubstitution M.toSeqData K h)
        (M.compose (M.right (discard M.toSeqData (QCtx.zero_discardable Γ)) A)
          (M.leftUnitor A))) = _
    rw [SeqData.tensor, M.toSeqData.exchange_right_pure _ _
      (M.toSeqData.compose_effect (M.toSeqData.right_effect A
        (discard_pure M.toSeqData (QCtx.zero_discardable Γ)))
        (M.toSeqData.leftUnitor_pure A))]
    have hcancel := congrArg (fun k => M.compose k
        (M.right (denoteSubstitution M.toSeqData K h) A))
      (newest_split_variable M Γ A (QCtx.zero_discardable Γ))
    exact (M.toSeqData.compose_assoc (split M.toSeqData ss)
      (M.left (packed Γ) (M.compose (M.right (discard M.toSeqData (QCtx.zero_discardable Γ)) A)
        (M.leftUnitor A))) (M.right (denoteSubstitution M.toSeqData K h) A)).symm.trans
        (hcancel.trans (M.toSeqData.identity_compose _))

/-- Transporting a substitution's raw function preserves its interpretation and guards. -/
theorem substitution_function_cast {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n}
    {e : ε} {σ σ' : Fin n → Term Φ m} (h : Substitution F Γ e σ Δ)
    (hs : σ = σ') (p : Polarity) (η : ε) :
    denoteSubstitution M.toSeqData K (hs ▸ h) = denoteSubstitution M.toSeqData K h ∧
      ((hs ▸ h).EffectAllowed p η ↔ h.EffectAllowed p η) := by
  cases hs
  exact ⟨rfl, Iff.rfl⟩

include N in
/-- The identity substitution has an allowed native representative after
normalizing annotations, and weakening its target composes to the identity. -/
theorem denoteSubstitution_identity_exists (p : Polarity) (η : ε) {n : Nat} (Γ : QCtx τ n) :
    ∃ (Θ : QCtx τ n) (w : QCtx.Weakening Θ Γ id)
      (h : Substitution F Γ (⊥ : ε) (Tm.bv : Fin n → Term Φ n) Θ),
      h.EffectAllowed p η ∧
        M.compose (denoteSubstitution M.toSeqData K h) (weaken M.toSeqData w) = M.identity (packed Γ) := by
  induction Γ using QCtx.inductionOn with
  | nil =>
    have hv : (Fin.elim0 : Fin 0 → Term Φ 0) = Tm.bv := funext (fun i => Fin.elim0 i)
    let h := hv ▸ Substitution.nil (F := F) (e := (⊥ : ε)) (Γ := (QCtx.nil : QCtx τ 0))
      (fun i => Fin.elim0 i)
    refine ⟨QCtx.nil, .refl QCtx.nil, h, ?_, ?_⟩
    · exact (substitution_function_cast M K _ hv p η).2.mpr trivial
    · rw [(substitution_function_cast M K _ hv p η).1, weaken_refl, M.toSeqData.compose_identity]
      change M.discard Silmaril.unit _ = M.identity _
      exact M.discard_unit _
  | @snoc n Γ A q ih =>
    obtain ⟨Θ, w, h, hg, he⟩ := ih
    have hv : Tm.upSub (Tm.bv : Fin n → Term Φ n) = Tm.bv := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    cases q with
    | zero =>
      obtain ⟨hl, hlg, hle⟩ := denoteSubstitution_rename_exists M K N p h hg Fin.succ
        (QCtx.Weakening.insertZero Γ A)
      let hz : Substitution F (Γ.snoc A .zero) (⊥ : ε) (Tm.upSub Tm.bv) (Θ.snoc A .zero) :=
        .zero hl (.bv 0) A
      let hz' := hv ▸ hz
      have wz : QCtx.Weakening (Θ.snoc A .zero) (Γ.snoc A .zero) id := by
        convert QCtx.Weakening.cons w (A := A) (q := .zero) (q' := .zero) le_rfl using 1
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      refine ⟨Θ.snoc A .zero, wz, hz', (substitution_function_cast M K hz hv p η).2.mpr hlg, ?_⟩
      rw [(substitution_function_cast M K hz hv p η).1]
      change M.compose (denoteSubstitution M.toSeqData K hl) (weaken M.toSeqData w) = M.identity (packed Γ)
      have hle' : denoteSubstitution M.toSeqData K hl = denoteSubstitution M.toSeqData K h := by
        simpa only [packed_snoc_zero, weaken_insertZero, M.toSeqData.identity_compose] using hle
      rw [hle']
      exact he
    | used q =>
      obtain ⟨hu, hug, hue⟩ := denoteSubstitution_upUsed_exists M K N p h hg A q
      let hu' := hv ▸ hu
      have wu : QCtx.Weakening (Θ.snoc A (.used (q ⊓ quantity A))) (Γ.snoc A (.used q)) id := by
        have hq : Usage.effective (.used q) (quantity A) ≤
            Usage.effective (.used (q ⊓ quantity A)) (quantity A) := by
          simp only [Usage.effective_used, inf_assoc, inf_idem]
          exact le_rfl
        convert QCtx.Weakening.cons w hq using 1
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      refine ⟨Θ.snoc A (.used (q ⊓ quantity A)), wu, hu',
        (substitution_function_cast M K hu hv p η).2.mpr hug, ?_⟩
      rw [(substitution_function_cast M K hu hv p η).1, hue]
      change M.compose (M.right (denoteSubstitution M.toSeqData K h) A)
        (M.right (weaken M.toSeqData w) A) = M.identity (product (packed Γ) A)
      rw [← M.toSeqData.right_compose, he, M.toSeqData.right_identity]

end Silmaril.Isotope.Refinement.Models.Denotation
