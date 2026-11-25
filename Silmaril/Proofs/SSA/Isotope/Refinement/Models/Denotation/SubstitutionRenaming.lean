module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionNaturality
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.Renaming

/-! # Renaming quantitative substitutions through their categorical interpretation -/

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
/-- Rename a substitution with both its effect allowance and categorical action preserved. -/
theorem denoteSubstitution_rename_exists (p : Polarity) {η : ε}
    {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n} {e : ε} {σ : Fin n → Term Φ m}
    (h : Substitution F Γ e σ Δ) (hh : h.EffectAllowed p η) :
    ∀ {k : Nat} {Θ : QCtx τ k} (ρ : Fin m → Fin k) (w : QCtx.Weakening Θ Γ ρ),
      ∃ h' : Substitution F Θ e (fun i => Tm.rename ρ (σ i)) Δ,
        h'.EffectAllowed p η ∧
        denoteSubstitution M.toSeqData K h' =
          M.compose (weaken M.toSeqData w) (denoteSubstitution M.toSeqData K h) := by
  induction h with
  | nil hd =>
    intro k Θ ρ w
    have hempty : (fun i : Fin 0 => Tm.rename ρ (Fin.elim0 i)) =
        (Fin.elim0 : Fin 0 → Term Φ k) := funext (fun i => Fin.elim0 i)
    rw [hempty]
    refine ⟨.nil (w.discardable hd), trivial, ?_⟩
    exact (M.toSeqData.pure_discard_natural _ (weaken_pure _ _) _ _).symm
  | @zero m n Γ Δ e σ h a A ih =>
    intro k Θ ρ w
    obtain ⟨h', hg, he⟩ := ih hh ρ w
    have hfun : (fun i => Tm.rename ρ (Fin.cases a σ i)) =
        Fin.cases (Tm.rename ρ a) (fun i => Tm.rename ρ (σ i)) :=
      funext (fun i => Fin.cases rfl (fun _ => rfl) i)
    rw [hfun]
    exact ⟨.zero h' (Tm.rename ρ a) A, hg, he⟩
  | @cons m n Γ Γl Γr Δ e el er σ a A q s h ha hq hc hl hr ih =>
    intro k Θ ρ w
    obtain ⟨Θr, Θl, ss, wr, wl, hlin⟩ := w.split_linearity s.symm
    obtain ⟨h', hg, he⟩ := ih hh.1 ρ wl
    obtain ⟨ha', hea⟩ := denote_rename_exists M K N ha ρ wr
    have hfun : (fun i => Tm.rename ρ (Fin.cases a σ i)) =
        Fin.cases (Tm.rename ρ a) (fun i => Tm.rename ρ (σ i)) :=
      funext (fun i => Fin.cases rfl (fun _ => rfl) i)
    rw [hfun]
    refine ⟨.cons ss.symm h' ha' (hq.trans hlin) hc hl hr, ⟨hg, hh.2⟩, ?_⟩
    change M.compose (split M.toSeqData ss.symm)
      (M.tensor (denoteSubstitution M.toSeqData K h') (denote M.toSeqData K ha')) = _
    rw [he, hea, ← M.toSeqData.tensor_comp_pure _ _ _ _ (weaken_pure _ wr),
      ← M.toSeqData.compose_assoc, ← weaken_split M w ss.symm s wl wr]
    exact M.toSeqData.compose_assoc _ _ _

/-- Inserting a zero slot leaves the packed weakening map unchanged. -/
theorem weaken_insertZero {n : Nat} (Γ : QCtx τ n) (A : τ) :
    weaken M.toSeqData (QCtx.Weakening.insertZero Γ A) = M.identity (packed Γ) := by
  have he := congrArg Subtype.val (weakenPure_skip M (QCtx.Weakening.refl Γ)
    (A := A) (q := .zero) le_rfl)
  exact he.trans (weaken_refl M.toSeqData Γ)

include N in
/-- Lifting an allowed substitution through a binder right-whiskers its action.
The fresh variable is pure and its annotation is normalized to its type quantity. -/
theorem denoteSubstitution_up_exists (p : Polarity) {η : ε}
    {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n} {e : ε} {σ : Fin n → Term Φ m}
    (h : Substitution F Γ e σ Δ) (hh : h.EffectAllowed p η) (A : τ) :
    ∃ h' : Substitution F (Γ.snoc A) e (Tm.upSub σ) (Δ.snoc A (.used (quantity A))),
      h'.EffectAllowed p η ∧
      denoteSubstitution M.toSeqData K h' = M.right (denoteSubstitution M.toSeqData K h) A := by
  obtain ⟨hl, hlg, hle⟩ := denoteSubstitution_rename_exists M K N p h hh Fin.succ
    (QCtx.Weakening.insertZero Γ A)
  let hv := HasType.var (F := F) (Φ := Φ) (e := (⊥ : ε)) 0
    (QCtx.varAllowed_snoc (QCtx.zero_discardable Γ) A)
  have hq : quantity A ≤ (Γ.zero.snoc A).linearity := by
    simp only [QCtx.linearity_snoc, QCtx.zero_linearity, Usage.linearity_used,
      inf_top_eq]
    exact le_rfl
  let ss := (QCtx.Split.zero_right Γ).snoc (.right (.used ⊤)) (A := A)
  let hu : Substitution F (Γ.snoc A) e (Tm.upSub σ) (Δ.snoc A (.used (quantity A))) :=
    .cons ss hl hv hq (EffectSystem.pure_commutes e).symm le_rfl bot_le
  refine ⟨hu, ⟨hlg, ?_, EffectSystem.pure_moves p η⟩, ?_⟩
  · rw [EffectSystem.quantity_pure]
    exact le_top
  · change M.compose (B := product (packed Γ) (product (packed Γ.zero) A))
      (split M.toSeqData ss)
      (M.tensor (A := packed Γ) (D := product (packed Γ.zero) A)
        (denoteSubstitution M.toSeqData K (Γ := Γ.snoc A .zero) hl)
        (denote M.toSeqData K (Γ := Γ.zero.snoc A) hv)) = _
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

end Silmaril.Isotope.Refinement.Models.Denotation
