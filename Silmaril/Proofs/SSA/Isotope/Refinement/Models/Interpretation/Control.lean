module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.Sequential
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.CaseEquations
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationOutput

/-! # Interpretation of categorical control representatives -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : CaseData.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (it : F.HasIter → ∀ {A B : τ}, M.Hom A (coprod B A) → M.Hom A B)
local notation "K" => ControlData.ofCase M F it

theorem denoteArrow_inlDeriv (cap : F.HasCase) (A B : τ) (e : ε) :
    denoteArrow M.toSeqData K (Syntactic.inlDeriv cap A B e) = M.inl A B := by
  change M.compose (M.leftUnitorInv A)
    (M.compose (Denotation.denote M.toSeqData K (Syntactic.identityDeriv A e)) (M.inl A B)) = _
  rw [denote_identityDeriv M.toSeqModel K, ← M.compose_assoc,
    M.toSeqData.leftUnitor_inv_hom, M.identity_compose]

theorem denoteArrow_inrDeriv (cap : F.HasCase) (A B : τ) (e : ε) :
    denoteArrow M.toSeqData K (Syntactic.inrDeriv cap A B e) = M.inr A B := by
  change M.compose (M.leftUnitorInv B)
    (M.compose (Denotation.denote M.toSeqData K (Syntactic.identityDeriv B e)) (M.inr A B)) = _
  rw [denote_identityDeriv M.toSeqModel K, ← M.compose_assoc,
    M.toSeqData.leftUnitor_inv_hom, M.identity_compose]

theorem denoteArrow_abortDeriv (cap : F.HasCase) (A : τ) (e : ε) :
    denoteArrow M.toSeqData K (Syntactic.abortDeriv cap A e) = M.abort A := by
  exact M.empty_hom_ext _ _

/-- A unit environment introduces no data to case branches. -/
theorem unit_desc {A B C : τ} (a : M.Hom (product Silmaril.unit A) C)
    (b : M.Hom (product Silmaril.unit B) C) :
    M.compose (M.leftUnitorInv (coprod A B))
      (M.compose (M.distribute Silmaril.unit A B) (M.desc a b)) =
      M.desc (M.compose (M.leftUnitorInv A) a) (M.compose (M.leftUnitorInv B) b) := by
  have h : M.compose (M.distribute Silmaril.unit A B) (M.desc a b) =
      M.compose (M.leftUnitor (coprod A B))
        (M.desc (M.compose (M.leftUnitorInv A) a) (M.compose (M.leftUnitorInv B) b)) := by
    apply M.distributed_hom_ext
    · rw [← M.compose_assoc, M.left_inl_distribute, M.inl_desc]
      simp only [← M.compose_assoc, M.toSeqData.leftUnitor_natural]
      simp only [M.compose_assoc, M.inl_desc, ← M.compose_assoc,
        M.toSeqData.leftUnitor_hom_inv, M.identity_compose]
    · rw [← M.compose_assoc, M.left_inr_distribute, M.inr_desc]
      simp only [← M.compose_assoc, M.toSeqData.leftUnitor_natural]
      simp only [M.compose_assoc, M.inr_desc, ← M.compose_assoc,
        M.toSeqData.leftUnitor_hom_inv, M.identity_compose]
  rw [h, ← M.compose_assoc, M.toSeqData.leftUnitor_inv_hom, M.identity_compose]

variable (N : ControlEnvironment (ControlData.ofCase M F it))
variable (H : WitnessCoherent M.toSeqModel (ControlData.ofCase M F it))
include N H in
theorem denoteArrow_descDeriv (cap : F.HasCase) {A B C : τ} {e : ε} {a b : Term Φ 1}
    (da : HasType F (Syntactic.input A) e a C)
    (db : HasType F (Syntactic.input B) e b C) :
    denoteArrow M.toSeqData K (Syntactic.descDeriv cap da db) =
      M.desc (denoteArrow M.toSeqData K da) (denoteArrow M.toSeqData K db) := by
  have hs : split M.toSeqData (Syntactic.inputSplit (coprod A B)) =
      M.leftUnitorInv (product Silmaril.unit (coprod A B)) :=
    eq_of_heq (split_zero_left M.toSeqData (Syntactic.input (coprod A B)))
  change M.compose (M.leftUnitorInv (coprod A B))
    (M.compose (split M.toSeqData (Syntactic.inputSplit (coprod A B)))
      (M.compose (M.left Silmaril.unit (Denotation.denote M.toSeqData K (Syntactic.identityDeriv _ e)))
        (M.compose (M.distribute Silmaril.unit A B)
          (M.desc
            (Denotation.denote M.toSeqData K (da.rename _ ((QCtx.Weakening.insertZero QCtx.nil _).up A)))
            (Denotation.denote M.toSeqData K (db.rename _ ((QCtx.Weakening.insertZero QCtx.nil _).up B))))))) = _
  rw [denote_continuation M.toSeqModel K N H, denote_continuation M.toSeqModel K N H,
    denote_identityDeriv M.toSeqModel K, hs]
  let x : M.Hom (product Silmaril.unit A) C := Denotation.denote M.toSeqData K da
  let y : M.Hom (product Silmaril.unit B) C := Denotation.denote M.toSeqData K db
  change M.compose (M.leftUnitorInv (coprod A B))
    (M.compose (M.leftUnitorInv (product Silmaril.unit (coprod A B)))
      (M.compose (M.left Silmaril.unit (M.leftUnitor (coprod A B)))
        (M.compose (M.distribute Silmaril.unit A B) (M.desc x y)))) = _
  have hu := congrArg (fun f => M.compose f (M.leftUnitorInv (coprod A B)))
    (M.toSeqData.unit_bind (M.leftUnitor (coprod A B)))
  simp only [M.compose_assoc, M.toSeqData.leftUnitor_hom_inv, M.compose_identity] at hu
  rw [← M.compose_assoc (M.leftUnitorInv (product Silmaril.unit (coprod A B))), hu,
    M.identity_compose]
  exact unit_desc M _ _

end Silmaril.Isotope.Refinement.Models.Interpretation
