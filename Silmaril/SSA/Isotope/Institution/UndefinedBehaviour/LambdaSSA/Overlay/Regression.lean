module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Thms

/-! The ordinary outcome projection identifies a saturated native region with
UB at an empty interface. Typed substitution into a nonempty interface
distinguishes them. -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.Institution.Observational
open Silmaril.Isotope.LambdaSSA (VCtx LCtx)
open Silmaril.Isotope.LambdaSSA.UB.Overlay

namespace LambdaSSARegionUBRegression

private abbrev τ := Ty Empty
private abbrev Γ : VCtx τ := []
private abbrev L : LCtx τ := []
private abbrev K : LCtx τ := [unit]

local instance : HasTy Unit τ := ⟨fun _ => unit, fun _ => unit⟩

private abbrev M : Model Unit 0 where
  α := Unit
  σ := Unit
  instr _ _ _ _ _ := False
  faults _ _ _ _ := True
  prim _ _ _ := True
  bound := Fin.elim0

private def prefixLoop : LambdaSSA.UB.Typed (Φ := Unit) Γ L :=
  LambdaSSA.UB.primitiveThenLoop Γ L () rfl

private def continuations (i : Fin L.length) :
    LambdaSSA.UB.Typed (Φ := Unit) (L.get i :: Γ) K :=
  Fin.elim0 i

private theorem nativeOutcomes_univ : nativeOutcomes prefixLoop M () = Set.univ := by
  have h := LambdaSSA.UB.observe_primitiveThenLoop_eq_empty M () (Γ := Γ) rfl
    (fun _ _ => trivial) (fun _ => Or.inl trivial)
  ext o
  change o.observation () ∈ LambdaSSA.UB.observe M prefixLoop ↔ o ∈ Set.univ
  rw [show LambdaSSA.UB.observe M prefixLoop = _ from h]
  cases o with
  | ret i _ _ => exact Fin.elim0 i
  | fault _ | diverge => exact ⟨fun _ => trivial, fun _ => trivial⟩

theorem projection_not_congruent :
    let p : Region Unit Γ L := .native prefixLoop
    let ub : Region Unit Γ L := .ub
    let k := fun i => Region.native (continuations i)
    (denote p M ()).possible = (denote ub M ()).possible ∧
      (denote (.lsubst p k) M ()).possible ≠ (denote (.lsubst ub k) M ()).possible := by
  constructor
  · exact nativeOutcomes_univ
  · rw [denote_ub_lsubst]
    change (Behaviour.bind (↑(nativeOutcomes prefixLoop M ()) : Behaviour 0 Unit Unit)
      (fun i a mid => (↑(nativeOutcomes (continuations i) (extendModel M a) mid) :
        Behaviour 1 Unit Unit))).possible ≠ Set.univ
    rw [Behaviour.coe_bind, nativeOutcomes_univ]
    exact bind_empty_ne_univ (i := (0 : Fin 1)) .unit () _

private def exit : LambdaSSA.UB.Typed (Φ := Unit) Γ K := ⟨.br 0 .unit, .br rfl .unit⟩

example : denote (.lsubst (K := L) (.native exit) (fun _ => .ub)) M () = ⊤ := by
  change (denote (.native exit) M ()).bind
    (fun i a mid => denote (.ub : Region Unit (K.get i :: Γ) L) (extendModel M a) mid) = ⊤
  apply Behaviour.bind_eq_top_of_reaches_top (i := (0 : Fin 1)) (a := .unit) (s := ())
  · exact LambdaSSA.Semantics.Region.Eval.br LambdaSSA.Semantics.Tm.Eval.unit
  · rfl

#print axioms LambdaSSA.UB.Overlay.native_refines_iff
#print axioms LambdaSSA.UB.Overlay.denote_native_lsubst
#print axioms LambdaSSA.UB.Overlay.lsubst_mono
#print axioms LambdaSSA.UB.Overlay.bind_empty_ne_univ
#print axioms projection_not_congruent

end LambdaSSARegionUBRegression
