module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.CaseSoundness

/-! # Case analysis whose branches use only their newest argument -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models
open Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace CaseData
variable (M : CaseData.{u,v,w,r} τ Φ ε)

/-- If neither branch uses its environment, case analysis discards that
environment and applies the coproduct fold to the scrutinee's value. -/
theorem case_return {D A B C : τ} (d : M.Hom D Silmaril.unit)
    (f : M.Hom A C) (g : M.Hom B C) :
    M.compose (M.distribute D A B)
      (M.desc (M.compose (M.compose (M.right d A) (M.leftUnitor A)) f)
        (M.compose (M.compose (M.right d B) (M.leftUnitor B)) g)) =
      M.compose (M.compose (M.right d (coprod A B)) (M.leftUnitor (coprod A B)))
        (M.desc f g) := by
  have h := congrArg (fun k => M.compose k (M.desc f g)) (M.case_eta d)
  simpa only [M.compose_assoc, M.desc_compose, M.inl_desc, M.inr_desc] using h

end CaseData

namespace Denotation
variable (M : CaseData.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (it : F.HasIter → ∀ {A B : τ}, M.Hom A (coprod B A) → M.Hom A B)

set_option backward.isDefEq.respectTransparency false in
/-- The codiagonal's case body folds the two continue alternatives together.
This constructs the actual typed body, without requiring witness coherence. -/
theorem denote_codiagonalBody_exists {n : Nat} {Γ : QCtx τ n} {e : ε}
    {b : Term Φ n} {A B : τ} (cap : F.HasCase)
    (hb : HasType F Γ e b (coprod (coprod B A) A)) :
    ∃ k : HasType F Γ e (.case b (.bv 0) (.inr (.bv 0))) (coprod B A),
      denote M.toSeqData (ControlData.ofCase M F it) k =
        M.compose (denote M.toSeqData (ControlData.ofCase M F it) hb)
          (M.desc (M.identity (coprod B A)) (M.inr B A)) := by
  let hl : HasType F (Γ.zero.snoc (coprod B A)) e (.bv 0 : Term Φ (n+1)) (coprod B A) :=
    .var 0 (QCtx.varAllowed_snoc (QCtx.zero_discardable Γ) (coprod B A))
  let hr : HasType F (Γ.zero.snoc A) e (.inr (.bv 0) : Term Φ (n+1)) (coprod B A) :=
    .inr cap (.var 0 (QCtx.varAllowed_snoc (QCtx.zero_discardable Γ) A))
  refine ⟨.case cap (QCtx.Split.zero_left Γ) hb hl hr, ?_⟩
  let d := discard M.toSeqData (QCtx.zero_discardable Γ)
  change M.compose (split M.toSeqData (QCtx.Split.zero_left Γ))
    (M.compose (M.left (packed Γ.zero) (denote M.toSeqData (ControlData.ofCase M F it) hb))
      (M.compose (M.distribute (packed Γ.zero) (coprod B A) A)
        (M.desc (M.compose (M.right d (coprod B A)) (M.leftUnitor (coprod B A)))
          (M.compose (M.compose (M.right d A) (M.leftUnitor A)) (M.inr B A))))) = _
  have h := M.case_return d (M.identity (coprod B A)) (M.inr B A)
  rw [M.compose_identity] at h
  rw [h]
  simpa only [M.compose_assoc] using congrArg
    (fun k => M.compose k (M.desc (M.identity (coprod B A)) (M.inr B A)))
    (zero_context_bind M.toSeqModel Γ
      (denote M.toSeqData (ControlData.ofCase M F it) hb) (QCtx.zero_discardable Γ))

end Denotation
end Silmaril.Isotope.Refinement.Models
