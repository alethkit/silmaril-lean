module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.WitnessCoherence
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionBinders
public import Silmaril.Raw.SSA.Isotope.Refinement.TypingSupport

/-! # Binder annotations in categorical beta reduction -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F) (N : ControlEnvironment K) (H : WitnessCoherent M K)
namespace Sequential

include N H in
/-- Changing a retained binder's annotation changes no packed wire. -/
theorem denote_binder_used {n : Nat} {Γ : QCtx τ n} {e η : ε}
    {b : Term Φ (n + 1)} {A B : τ} {q : Quantity}
    (hb : HasType F (Γ.snoc A (.used q)) e b B)
    (hd : HasType F (Γ.snoc A) η b B) : denote M.toSeqData K hd = denote M.toSeqData K hb := by
  let w : QCtx.Weakening (Γ.snoc A) (Γ.snoc A (.used q)) id :=
    .ofPointwise (fun i => Fin.cases rfl (fun _ => rfl) i) (fun i => by
      cases i using Fin.cases with
      | zero =>
        change q ⊓ quantity A ≤ ⊤ ⊓ quantity A
        exact inf_le_inf le_top le_rfl
      | succ j => exact le_rfl)
  have hw : weaken M.toSeqData w = M.identity (product (packed Γ) A) := by
    change M.right (weaken M.toSeqData (QCtx.Weakening.refl Γ)) A = _
    rw [weaken_refl, M.toSeqData.right_identity]
  let k : HasType F (Γ.snoc A) η (Tm.rename id b) B := (Tm.rename_id b).symm ▸ hd
  have hc : denote M.toSeqData K k = denote M.toSeqData K hd :=
    denote_syntax_cast M K hd (Tm.rename_id b).symm
  have hn := denote_rename_of_typing M K N H hb id w k
  have hz : M.compose (weaken M.toSeqData w) (denote M.toSeqData K hb) = denote M.toSeqData K hb :=
    (congrArg (fun f : M.Hom (product (packed Γ) A) (product (packed Γ) A) =>
      M.compose f (denote M.toSeqData K hb)) hw).trans (M.toSeqData.identity_compose _)
  exact hc.symm.trans (hn.trans hz)

/-- If a body accepts both zero and ordinary usage, the ordinary value is discardable. -/
theorem zero_binder_affine {n : Nat} {Γ : QCtx τ n} {e η : ε}
    {b : Term Φ (n + 1)} {A B : τ}
    (hb : HasType F (Γ.snoc A .zero) e b B)
    (hd : HasType F (Γ.snoc A) η b B) : Quantity.affine ≤ quantity A := by
  have hu : Term.uses b 0 = false := by
    cases h : Term.uses b 0 with
    | false => rfl
    | true => exact False.elim (hb.used_nonzero h rfl)
  have he := hd.unused_discardable hu
  have he' : Usage.zero ≤ Usage.used (quantity A) := by
    simpa only [QCtx.effective, QCtx.snoc_zero, Usage.effective, Usage.used_mul_used,
      top_inf_eq] using he
  exact (Usage.zero_le_used _).mp he'

include N H in
/-- The ordinary interpretation of a zero-use binder first discards that wire. -/
theorem denote_binder_zero {n : Nat} {Γ : QCtx τ n} {e η : ε}
    {b : Term Φ (n + 1)} {A B : τ}
    (hb : HasType F (Γ.snoc A .zero) e b B)
    (hd : HasType F (Γ.snoc A) η b B) (hA : Quantity.affine ≤ quantity A) :
    denote M.toSeqData K hd = M.compose
      (M.compose (M.left (packed Γ) (M.discard A hA)) (M.rightUnitor (packed Γ)))
      (denote M.toSeqData K (Γ := Γ.snoc A .zero) hb) := by
  let w : QCtx.Weakening (Γ.snoc A) (Γ.snoc A .zero) id :=
    .ofPointwise (fun i => Fin.cases rfl (fun _ => rfl) i) (fun i => by
      cases i using Fin.cases with
      | zero =>
        change Usage.zero ≤ Usage.effective (.used ⊤) (quantity A)
        simpa only [Usage.effective, Usage.used_mul_used, top_inf_eq] using (Usage.zero_le_used _).mpr hA
      | succ j => exact le_rfl)
  have hw : weaken M.toSeqData w =
      M.compose (M.left (packed Γ) (M.discard A hA)) (M.rightUnitor (packed Γ)) := by
    change M.compose (M.right (weaken M.toSeqData (QCtx.Weakening.refl Γ)) A)
      (M.compose (M.left (packed Γ) (M.discard A hA)) (M.rightUnitor (packed Γ))) = _
    rw [weaken_refl, M.toSeqData.right_identity, M.toSeqData.identity_compose]
  let k : HasType F (Γ.snoc A) η (Tm.rename id b) B := (Tm.rename_id b).symm ▸ hd
  have hc : denote M.toSeqData K k = denote M.toSeqData K hd :=
    denote_syntax_cast M K hd (Tm.rename_id b).symm
  have hn := denote_rename_of_typing M K N H hb id w k
  exact hc.symm.trans (hn.trans (congrArg (fun f => M.compose f (denote M.toSeqData K (Γ := Γ.snoc A .zero) hb)) hw))

end Sequential
end Silmaril.Isotope.Refinement.Models.Denotation
