module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.CaseSoundness

/-! # Binding the newest variable is the identity on a continuation -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : CaseData.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (it : F.HasIter → ∀ {A B : τ}, M.Hom A (coprod B A) → M.Hom A B)
local notation "K" => ControlData.ofCase M F it

/-- The native identity-binding witness has the original denotation. No beta
soundness or typing-coherence theorem is needed for this structural equation. -/
theorem denote_identityBind_exists (N : ControlEnvironment K)
    {n : Nat} {Γ : QCtx τ n} {e : ε} {b : Term Φ (n + 1)} {A B : τ}
    (hb : HasType F (Γ.snoc A) e b B) :
    ∃ k : HasType F (Γ.snoc A) e (.let₁ (.bv 0) b.underBinder) B,
      denote M.toSeqData K k = denote M.toSeqData K hb := by
  obtain ⟨kb, hkb⟩ := denote_underBinder_zero_exists M it N (A := A) hb
  let hv : HasType F (Γ.zero.snoc A) e (.bv 0 : Term Φ (n+1)) A :=
    .var 0 (QCtx.varAllowed_snoc (QCtx.zero_discardable Γ) A)
  let si := (QCtx.Split.zero_right Γ).snoc (.right (.used ⊤)) (A := A)
  let ki := HasType.let₁ si hv kb
  refine ⟨ki, ?_⟩
  change M.compose (split M.toSeqData si)
    (M.compose (M.left (packed Γ) (denote M.toSeqData K hv)) (denote M.toSeqData K kb)) = _
  rw [hkb, ← M.compose_assoc]
  change M.compose (M.compose (split M.toSeqData si)
    (M.left (packed Γ) (M.compose (M.right (discard M.toSeqData (QCtx.zero_discardable Γ)) A)
      (M.leftUnitor A)))) _ = _
  rw [newest_split_variable M.toSeqModel Γ A (QCtx.zero_discardable Γ)]
  exact M.identity_compose _

end Silmaril.Isotope.Refinement.Models.Denotation
