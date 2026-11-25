module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.ContextStepActs

/-! # Reifying iteration by the native uniformity rule

The comparison map packs the persistent context together with the current
state. The proved contextual-step action is its commuting square. Applying
both directed pure uniformity rules identifies the categorical loop with the
source iteration, without a semantic fixed-point assumption.
-/

@[expose] public section
noncomputable section
universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless Denotation

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- A closed arrow can be placed above a discardable ambient context. -/
def atDiscardDeriv {n : Nat} (Γ : QCtx τ n) (hd : Γ.Discardable)
    {e : ε} {f : Term Φ 1} {A B : τ} (hf : HasType F (input A) e f B) :
    HasType F (Γ.snoc A) e (atIndex 0 f) B := by
  have hw := (QCtx.Weakening.empty Γ hd).up A
  have hh := hf.rename _ hw
  have hρ : Tm.up (Fin.elim0 : Fin 0 → Fin n) = (fun _ : Fin 1 => (0 : Fin (n + 1))) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hρ] at hh
  exact hh

/-- The native categorical loop, including environment copy and discard,
acts exactly as the written iteration constructor. -/
theorem native_iteration_acts (hR : R.RenamingClosed) :
    IterationActs (ε := ε) (F := F) (R := R) hR := by
  intro n Γ Γl Γr a b A B cap s hΓl hu ha f hbody hc hd
  have cc := iter_hasCase cap
  have hdΓ := QCtx.discardable_iff_linearity.mpr
    (show Quantity.affine ≤ Γl.linearity from hu ▸ le_top)
  have ss := QCtx.split_self_of_relevant (Γ := Γl) (hu ▸ le_top)
  obtain ⟨r, hr, hsquare⟩ := contextStep_pack_acts (R := R) hR cc hΓl hu hbody hc hd
  obtain ⟨dr⟩ := r.property
  obtain ⟨db⟩ := hbody.wellTyped
  have ds := packDeriv (F := F) (Φ := Φ) (Γl.snoc A) (⊥ : ε)
  have dc := HasType.var (F := F) (Φ := Φ) (e := (⊤ : ε)) 0
    (QCtx.discardable_varAllowed hdΓ B)
  have dstep := atDiscardDeriv Γl hdΓ dr
  have initialActs := Acts.of_equates (r := iterateArrow cap r)
    (action_iterate (R := R) cap ds.top dr)
  have hleft := initialActs.bind_pack s ha
  have dit : HasType F Γ (⊤ : ε) (.iter a b) B :=
    .iter cap s hu EffectSystem.iterable_top ha db
  have hright := action_identity (R := R) dit
  have hp : (packTerm (Φ := Φ) (Γl.snoc A)).underBinder =
      .pair (packTerm Γl).lift.lift (.bv 0) := by
    change Tm.pair (Tm.rename (Tm.up Fin.succ) (packTerm Γl).lift) (.bv 0) = _
    rw [Tm.rename_lift]
    rfl
  have hsq : Equates (ε := ε) F R (Γl.snoc A)
      (.let₁ (packTerm (Γl.snoc A)) (atIndex 0 r.val).underBinder)
      (.case b (.inl ((.bv 0 : Term Φ (n + 1)).underBinder))
        (.inr (packTerm (Γl.snoc A)).underBinder)) (coprod B (product (packed Γl) A)) := by
    rw [underBinder_atIndex_zero, hp]
    exact hsquare
  have heq : Equates (ε := ε) F R Γ
      (.let₁ a (.iter (packTerm (Γl.snoc A)) (atIndex 0 r.val).underBinder))
      (.let₁ (.iter a b) (.bv 0)) B := by
    have law (p : Polarity) := UniformityRule.square (ε := ε) (p := p) cap s ss hu
      EffectSystem.iterable_top ha ds dstep db dc (EffectSystem.pure_moves p ⊤)
    have lhs : WellTyped (ε := ε) F Γ
        (.let₁ a (.iter (packTerm (Γl.snoc A)) (atIndex 0 r.val).underBinder)) B := by
      simpa only [underBinder_atIndex_zero] using hleft.wellTyped
    have rhs : WellTyped (ε := ε) F Γ (.let₁ (.iter a b) (.bv 0)) B := by
      simpa only [action, atIndex, Tm.rename] using hright.1.wellTyped.1
    have directed (p : Polarity) := Refines.uniformity (R := R) p (law p) lhs rhs
      (by cases p with
        | positive => exact hsq.1
        | negative => exact hsq.2)
    exact ⟨directed .positive, directed .negative⟩
  have heq' : Equates (ε := ε) F R Γ
      (.let₁ a (.iter (packTerm (Γl.snoc A)) (atIndex 0 r.val))) (.iter a b) B := by
    rw [underBinder_atIndex_zero] at heq
    exact heq.trans hright
  have hfinal := hleft.output heq'
  change Acts Γ (.pair (packTerm Γl) a)
    (iterate (R := R) hR cap
      ((nativeControl (ε := ε) (F := F) (R := R) hR).contextStep cc (packed Γl) hc hd f)) (.iter a b)
  rw [← hr]
  exact hfinal

end Silmaril.Isotope.Refinement.Models.Syntactic
