module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.ControlReification

/-! # Reification of the retained environment in an iteration step

The loop environment is unrestricted by the native typing premise. Copying its
packing, feeding one copy to the body, and discarding the exit copy are native
quantitative equations, including contexts with omitted slots.
-/

@[expose] public section
noncomputable section
universe u v w

namespace Silmaril.Isotope.Refinement

namespace QCtx
variable {τ : Type u} [HasQuantity τ]

theorem split_self_of_relevant {n : Nat} {Γ : QCtx τ n}
    (h : Quantity.relevant ≤ Γ.linearity) : Γ.Split Γ Γ := by
  intro i
  refine ⟨rfl, rfl, ?_⟩
  rcases (Usage.le_linearity_iff _ _ _).mp ((le_linearity_iff.mp h) i) with hz | hu
  · rw [hz]
    exact .left .zero
  · exact .both _ hu

theorem discardable_varAllowed {n : Nat} {Γ : QCtx τ n} (h : Γ.Discardable) (A : τ) :
    (Γ.snoc A).VarAllowed 0 := by
  constructor
  · change Usage.effective (.used .linear) (quantity A) ≤ Usage.effective (.used ⊤) (quantity A)
    simp only [Usage.effective_used, Usage.used_le_used, top_inf_eq]
    exact inf_le_right
  · intro i hi
    cases i using Fin.cases with
    | zero => exact False.elim (hi rfl)
    | succ i => exact h i

end QCtx
namespace Models.Syntactic

open LetIter.LocallyNameless Denotation

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- The exit branch drops the retained environment and injects its result. -/
def nativeExit (hR : R.RenamingClosed) (cap : F.HasCase) (D B S : τ)
    (hd : Quantity.affine ≤ quantity D) : Hom (ε := ε) F R (product D B) (coprod B S) :=
  compose hR (right hR (discard D hd) B) (compose hR (leftUnit B) (inl cap B S))

theorem exit_pack_acts (hR : R.RenamingClosed) {n : Nat} {Γ : QCtx τ n}
    (cap : F.HasCase) (hΓ : Γ.DefaultAnnotations) (hd : Γ.Discardable)
    (B S : τ) (hq : Quantity.affine ≤ quantity (packed Γ)) :
    Acts (Γ.snoc B) (packTerm (Γ.snoc B)) (nativeExit (ε := ε) (R := R) hR cap (packed Γ) B S hq)
      (.inl (.bv 0)) := by
  have dp := packDeriv (F := F) (Φ := Φ) Γ (⊥ : ε)
  have dl := dp.rename Fin.succ (.insertZero Γ B)
  have dv := zeroParameter (F := F) (Φ := Φ) Γ B (.used ⊤) (⊥ : ε) (by
    change Quantity.linear ⊓ quantity B ≤ ⊤ ⊓ quantity B
    exact inf_le_inf bot_le le_rfl)
  have sp := (QCtx.Split.zero_right Γ).snoc (A := B) (.right (.used ⊤))
  have hc := (Acts.discard (R := R) dp hq (packed_quantity_eq hΓ).le).rename hR
    Fin.succ (.insertZero Γ B)
  have h₀ := hc.right hR sp dl.top dv (zero_parameter_bound Γ B)
  have h₁ := Acts.leftUnit_variable (F := F) (R := R) (ε := ε) hR
    (hΓ.snoc B (.inr rfl)) 0 (QCtx.discardable_varAllowed hd B)
  have db := HasType.var (F := F) (Φ := Φ) (e := (⊤ : ε)) 0 (QCtx.discardable_varAllowed hd B)
  have h₂ := Acts.inl (R := R) (B := S) cap db
  exact h₀.compose hR (HasType.pair sp dl dv).top
    (h₁.compose hR (HasType.pair (QCtx.Split.zero_left _) (.unit (QCtx.zero_discardable _)) db) h₂)

set_option maxHeartbeats 1000000 in
/-- A contextual iteration step is exactly its source body, except that the
continuation branch carries the packed persistent environment. -/
theorem contextStep_pack_acts (hR : R.RenamingClosed) {n : Nat} {Γ : QCtx τ n}
    {b : Term Φ (n + 1)} {A B : τ} (cap : F.HasCase)
    (hΓ : Γ.DefaultAnnotations) (hu : Γ.linearity = ⊤)
    {f : Hom (ε := ε) F R (product (packed Γ) A) (coprod B A)}
    (h : Acts (Γ.snoc A) (packTerm (Γ.snoc A)) f b)
    (hc : Quantity.relevant ≤ quantity (packed Γ))
    (hd : Quantity.affine ≤ quantity (packed Γ)) :
    Acts (Γ.snoc A) (packTerm (Γ.snoc A))
      ((nativeControl (ε := ε) (F := F) (R := R) hR).contextStep cap (packed Γ) hc hd f)
      (.case b (.inl (.bv 0)) (.inr (.pair (packTerm Γ).lift.lift (.bv 0)))) := by
  have ds := QCtx.split_self_of_relevant (Γ := Γ) (hu ▸ le_top)
  have discardΓ := QCtx.discardable_iff_linearity.mpr (show Quantity.affine ≤ Γ.linearity from hu ▸ le_top)
  have dp := packDeriv (F := F) (Φ := Φ) Γ (⊥ : ε)
  have dl := dp.rename Fin.succ (.insertZero Γ A)
  have dv := zeroParameter (F := F) (Φ := Φ) Γ A (.used ⊤) (⊥ : ε) (by
    change Quantity.linear ⊓ quantity A ≤ ⊤ ⊓ quantity A
    exact inf_le_inf bot_le le_rfl)
  have sp := (QCtx.Split.zero_right Γ).snoc (A := A) (.right (.used ⊤))
  have sc := ds.snoc (A := A) (.left .zero)
  have sr := ds.snoc (A := A) (.right (.used ⊤))
  have qp := pack_lift_bound hΓ A
  have qv := zero_parameter_bound Γ A
  have hcopy := (Acts.copy (R := R) dp hc (packed_quantity_eq hΓ).le).rename hR
    Fin.succ (.insertZero Γ A)
  have h₀ := hcopy.right hR sp dl.top dv qv
  have h₁ := Acts.assoc (R := R) sp sc dl dl dv qp qp qv
  have h₂ := h.left hR sr dl.top (packDeriv _ (⊤ : ε))
  obtain ⟨db⟩ := h.wellTyped
  have h₃ := Acts.of_equates (r := distributorInvArrow cap (packed Γ) B A)
    (distributorInv_action (R := R) cap sr dl db qp)
  have hzero : (Γ.snoc A .zero).Discardable := by
    intro i
    exact Fin.cases le_rfl (fun j => discardΓ j) i
  have hΓzero := hΓ.snoc A (.inl rfl)
  have hExit := exit_pack_acts (ε := ε) (F := F) (R := R) hR cap hΓzero hzero B (product (packed Γ) A) hd
  have hL := hExit.desc_inl hR cap (packDeriv _ (⊤ : ε))
    (inr (R := R) cap B (product (packed Γ) A))
  have hright := (Acts.inr (R := R) (A := B) cap
    (packDeriv ((Γ.snoc A .zero).snoc A) (⊤ : ε))).desc_inr hR cap
    (packDeriv ((Γ.snoc A .zero).snoc A) (⊤ : ε))
    (nativeExit hR cap (packed Γ) B (product (packed Γ) A) hd)
  have h₄ := hL.case hR cap sr db (.inl cap (packDeriv _ (⊤ : ε)))
    (.inr cap (packDeriv _ (⊤ : ε))) hright
  have h34 := h₃.compose hR (HasType.pair sr dl.top db) h₄
  have h234 := h₂.compose hR (HasType.pair sr dl.top (packDeriv _ (⊤ : ε))) h34
  have h1234 := h₁.compose hR (HasType.pair sp (.pair sc dl dl) dv).top h234
  have hall := h₀.compose hR (packDeriv (Γ.snoc A) (⊤ : ε)) h1234
  change Acts _ _ ((seqData (ε := ε) (F := F) (R := R) hR).compose
    ((seqData hR).right ((seqData hR).copy (packed Γ) hc) A)
    ((seqData hR).compose ((seqData hR).associator (packed Γ) (packed Γ) A)
      ((seqData hR).compose ((seqData hR).left (packed Γ) f)
        ((seqData hR).compose (distributorInv cap (packed Γ) B A)
          (desc hR cap
            ((seqData hR).compose ((seqData hR).right ((seqData hR).discard (packed Γ) hd) B)
              ((seqData hR).compose ((seqData hR).leftUnitor B) (inl cap B (product (packed Γ) A))))
            (inr cap B (product (packed Γ) A))))))) _
  simp only [seqData_copy, seqData_discard, seqData_right, seqData_left, seqData_associator,
    seqData_leftUnitor, seqData_compose]
  exact hall

end Models.Syntactic
end Silmaril.Isotope.Refinement
