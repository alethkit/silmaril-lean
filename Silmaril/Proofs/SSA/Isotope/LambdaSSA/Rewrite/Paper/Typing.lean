module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ProductEta.Step.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Uniformity.Thms

/-! # Exact endpoints of the opt-in relation -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper

variable {τ : Type u} [Silmaril.TypeFormers τ] {Φ : Type v} [Silmaril.HasTy Φ τ]

theorem typed {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Eqv Γ r s L) :
    HasType Γ r L ∧ HasType Γ s L := by
  induction h with
  | cfgEta h => exact h.typed
  | productBeta h => exact h.typed
  | productEta h => exact h.typed
  | symm _ ih => exact ih.symm
  | trans _ _ il ir => exact ⟨il.1, ir.2⟩
  | let₁ ha _ ih => exact ⟨.let₁ ha ih.1, .let₁ ha ih.2⟩
  | let₂ ha _ ih => exact ⟨.let₂ ha ih.1, .let₂ ha ih.2⟩
  | case ha _ _ il ir => exact ⟨.case ha il.1 ir.1, .case ha il.2 ir.2⟩
  | cfg R _ _ ie ib => exact ⟨.cfg R ie.1 (fun i => (ib i).1), .cfg R ie.2 (fun i => (ib i).2)⟩
  | lsubstCongr hp _ ih =>
    exact ⟨hp.hasType.lsubst (fun _ _ hi => (ih hi).1),
      hp.hasType.lsubst (fun _ _ hi => (ih hi).2)⟩
  | lsubstPost _ hr hs hσ _ => exact ⟨hr.hasType.lsubst hσ, hs.hasType.lsubst hσ⟩
  | collapsePost he hp hσ =>
    exact ⟨(CfgEta.Codiagonal.nested_typed he.hasType hp.hasType).lsubst hσ,
      (CfgEta.Codiagonal.flattened_typed he.hasType hp.hasType).lsubst hσ⟩
  | uniform he hp hq ha _ _ =>
    exact ⟨.cfg (fun _ : Fin 1 => _) he.hasType (fun _ => hp.hasType),
      .cfg (fun _ : Fin 1 => _) (he.hasType.lsubst (CfgEta.Uniformity.localMap_typed ha.hasType))
        (fun _ => hq)⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
