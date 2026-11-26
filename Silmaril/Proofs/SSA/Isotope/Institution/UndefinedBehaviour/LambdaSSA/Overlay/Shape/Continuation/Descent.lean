module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Defs
public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Observation
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Context
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.ControlRules
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.ValueRules

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {α : Type w} {σ : Type x}
  {Γ L K : List (Ty κ)} {r t : Region Φ}

local notation "Obs" => ShapedObs (Φ := Φ) (κ := κ) (α := α) (σ := σ)

private theorem rewrite_obs (h : Region.RewriteEquiv Γ r t L) : Obs Γ r t := by
  induction h with
  | entry h => exact .of_obs (UB.Overlay.cfgEquiv_obs h)
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case ha il ir
  | cfg R he hb ie ib => exact .cfg R he.typed.1 (fun i => (hb i).typed.1) ie ib
  | letBr ha _ _ => exact fun _ _ _ _ _ => letValue ha
  | caseInl _ _ _ => exact fun _ _ _ _ _ => caseInl
  | caseInr _ _ _ => exact fun _ _ _ _ _ => caseInr

theorem substitution_obs (h : Region.SubstitutionEquiv Γ r t L) : Obs Γ r t := by
  induction h with
  | base h => exact rewrite_obs h
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case ha il ir
  | cfg R he hb ie ib => exact .cfg R he.typed.1 (fun i => (hb i).typed.1) ie ib
  | letValue ha _ => exact fun _ _ _ _ _ => letValue ha
  | caseValue ha _ => exact caseValue ha
  | caseCfg he hl hr => exact fun _ _ _ _ _ => caseCfg he hl hr
  | initial ha _ _ => exact initial ha
  | cfgOutward => exact fun _ _ _ _ _ => cfgOutward _ _ _

theorem substitutionEquiv_denote (h : Region.SubstitutionEquiv Γ r t L)
    (M : UB.Overlay.Shape.Model.{u,v,w,x} Φ Γ) (s : M.raw.σ) :
    UB.Overlay.Shape.denote (.native ⟨r, h.typed.1⟩) M s = UB.Overlay.Shape.denote (.native ⟨t, h.typed.2⟩) M s := by
  let O : Ops Φ M.raw.α M.raw.σ := ⟨M.raw.instr, M.raw.faults, M.raw.prim⟩
  have obs := (substitution_obs h) O M.atomType M.instrTyped (envOfBound M.raw.bound) (UB.Overlay.Shape.env_typed M)
  simp only [UB.Overlay.Shape.denote, UB.Overlay.denote, WithTop.coe_inj]
  apply Set.ext
  intro o
  simp only [UB.Overlay.mem_nativeOutcomes_iff _ (envOfBound_agrees M.raw.bound)]
  cases o with
  | ret i a t => exact obs.eval
  | fault t => exact obs.fault
  | diverge => exact obs.div

theorem familyDenotation_eq {f g : Region.ContinuationFamily (Φ := Φ) Γ L K}
    (h : (Region.continuationSetoid (Φ := Φ) Γ L K).r f g) :
    UB.Overlay.Shape.Continuation.familyDenotation.{u,v,w,x} f = UB.Overlay.Shape.Continuation.familyDenotation.{u,v,w,x} g := by
  funext i M s
  have rel := h (ℓ := i.val) (A := L.get i) (List.getElem?_eq_getElem i.isLt)
  exact substitutionEquiv_denote rel M s

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation
