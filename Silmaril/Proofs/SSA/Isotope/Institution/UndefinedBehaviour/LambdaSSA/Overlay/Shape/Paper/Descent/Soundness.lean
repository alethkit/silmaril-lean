module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Defs
public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Observation
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Interpretation
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Descent.Contexts
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Descent.Eta
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Descent.Product
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Descent
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Context
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.Morphism.SSAIter (envOfBound)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation
  (Ops ShapedObs substitution_obs)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity
  (regionAt_to_denote denote_to_regionAt)
open Silmaril.Isotope.LambdaSSA.Region (ContinuationFamily)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {α : Type w} {σ : Type x}
  {Γ L K : List (Ty κ)} {r t : LambdaSSA.Region Φ}

local notation "Obs" => ShapedObs (Φ := Φ) (κ := κ) (α := α) (σ := σ)

private theorem obs_denote (r t : UB.Typed (Φ := Φ) Γ L)
    (obs : ∀ (α : Type w) (σ : Type x), ShapedObs (α := α) (σ := σ) Γ r.val t.val)
    (M : Shape.Model.{u,v,w,x} Φ Γ) (s : M.raw.σ) :
    Shape.denote (.native r) M s = Shape.denote (.native t) M s :=
  regionAt_to_denote M r t s
    (obs M.raw.α M.raw.σ ⟨M.raw.instr, M.raw.faults, M.raw.prim⟩ M.atomType M.instrTyped
      (envOfBound M.raw.bound) (Shape.env_typed M))

private theorem denote_obs (r t : UB.Typed (Φ := Φ) Γ L)
    (obs : ∀ (M : Shape.Model.{u,v,w,x} Φ Γ) (s : M.raw.σ),
      Shape.denote (.native r) M s = Shape.denote (.native t) M s) : Obs Γ r.val t.val := by
  intro O types primitive env typed
  let M : Shape.Model.{u,v,w,x} Φ Γ := {
    raw := ⟨α, σ, O.instr, O.faults, O.prim, fun i => env i.val⟩
    atomType := types
    boundTyped := fun i => typed (List.getElem?_eq_getElem i.isLt)
    instrTyped := primitive }
  exact denote_to_regionAt M (runtime := env) (fun _ => rfl) r t (obs M)

private theorem cfgEta_obs (h : Region.CfgEta.Eqv Γ r t L) : Obs Γ r t := by
  induction h with
  | native h => exact substitution_obs h
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case ha il ir
  | cfg R he hb ie ib => exact .cfg R he.typed.1 (fun i => (hb i).typed.1) ie ib
  | etaPost he hb _ => exact fun _ _ _ _ _ => etaPost he hb _

theorem eqv_obs (h : Region.Paper.Eqv Γ r t L) :
    ∀ (α : Type w) (σ : Type x), ShapedObs (α := α) (σ := σ) Γ r t := by
  induction h <;> intro α σ
  case cfgEta h => exact cfgEta_obs h
  case productBeta h => exact productBeta h
  case productEta h => exact denote_obs ⟨_, h.typed.1⟩ ⟨_, h.typed.2⟩ (Shape.product_eta h)
  case symm _ ih => exact (ih α σ).symm
  case trans _ _ ih ik => exact (ih α σ).trans (ik α σ)
  case let₁ ha _ ih => exact .let₁ ha (ih α σ)
  case let₂ ha _ ih => exact .let₂ ha (ih α σ)
  case case ha _ _ il ir => exact .case ha (il α σ) (ir α σ)
  case cfg R he hb ie ib => exact .cfg R he.typed.1 (fun i => (hb i).typed.1) (ie α σ) (fun i => ib i α σ)
  case lsubstCongr hp _ ih => exact lsubstCongr hp (fun _ _ hi => ih hi α σ)
  case lsubstPost _ hr ht _ ih => exact lsubstPost hr ht (ih α σ) _
  case substVars h hθ ih => exact substVars h.typed.1 h.typed.2 (ih α σ) hθ
  case renameLabels _ _ ih => exact renameLabels (ih α σ) _
  case collapsePost he hp hk => exact denote_obs _ _ (Shape.Paper.collapsePost he hp hk)
  case uniform he hp hq ha _ ih =>
    exact denote_obs (Shape.Paper.uniformSource he hp) (Shape.Paper.uniformTarget he hq ha)
      (Shape.Paper.uniform_of_observed_square he hp hq ha
        (obs_denote (Shape.Paper.squareLeft hp ha) (Shape.Paper.squareRight hq ha) ih))

theorem eqv_denote (h : Region.Paper.Eqv Γ r t L)
    (M : Shape.Model.{u,v,w,x} Φ Γ) (s : M.raw.σ) :
    Shape.denote (.native ⟨r, h.typed.1⟩) M s = Shape.denote (.native ⟨t, h.typed.2⟩) M s :=
  obs_denote _ _ (eqv_obs h) M s

theorem familyDenotation_eq {f g : ContinuationFamily (Φ := Φ) Γ L K}
    (h : (Region.Paper.familySetoid (Φ := Φ) Γ L K).r f g) :
    Shape.Continuation.familyDenotation.{u,v,w,x} f = Shape.Continuation.familyDenotation.{u,v,w,x} g := by
  funext i M s
  exact eqv_denote (h (List.getElem?_eq_getElem i.isLt)) M s

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent
