module

public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Thms

/-! # Adequacy of the actual numbered nested θ graph -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open OrderedTheta (carried results carriedData resultData point pack)
open OrderedRuntime.Structured
open TwoBlock.TwoExit (callCase)
open Silmaril.Elgot
open NestedTheta (stepWith)
open Acyclic.Theta.ExplicitRuntime.Wiring (read_newest read_nextRuntime)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B K D Q : τ}

local notation "model" => wireModel (Φ := Φ) (ε := ε) (σ := σ)

private theorem point_eta (out : Point σ Q) :
    point (out.get .head) (out.get (.tail .head)) = out := by
  cases out with
  | cons value tail =>
    cases tail with
    | cons token tail => cases tail; rfl

private theorem step_eta (out : StepResult σ Q) :
    Tuple.cons (out.get .head) (point (out.get (.tail .head)) (out.get (.tail (.tail .head)))) = out := by
  cases out with
  | cons tag tail =>
    cases tail with
    | cons value tail =>
      cases tail with
      | cons token tail => cases tail; rfl

private theorem decode_step (r : TyDen D ⊕ TyDen A) (token : σ) :
    decode (ts := results (Carrier A D)) (encodeStep (A := A) (D := D) r, token) = tagged (r, token) := by
  cases r <;> rfl

private theorem enter_wire (op : TwoBlock.Instruction Φ A B) (a : TyDen A) (token : σ) :
    (model).primitive (.ordered (carriedData (Carrier A D)) (carriedData (Carrier B K)) (.effect (.enter op)))
      (entryTuple (a, token)) =
      Part.map entryTuple ((TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) op a).run token) := by
  change Part.map (decode (ts := carried (Carrier B K)))
    (((match TypeModel.coprodEquiv D A (start a) with
    | .inr x => TwoBlock.call (ε := ε) op x >>= fun b => pure (pack (start b))
    | .inl _ => StateT.mk fun _ => Part.none) : StateT σ Part.{u} _).run token) = _
  rw [start, Equiv.apply_symm_apply]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  rfl

private theorem inner_wire (op : TwoBlock.Instruction Φ B (Carrier B K)) (b : TyDen B) (token : σ) :
    (model).primitive (.ordered (carriedData _) (resultData _) (.effect (.inner op)))
      (entryTuple (b, token)) =
      Part.map tagged ((callCase (ε := ε) (m := StateT σ Part.{u}) op b).run token) := by
  change Part.map (decode (ts := results (Carrier B K)))
    (((match TypeModel.coprodEquiv K B (start b) with
    | .inr x => callCase (ε := ε) op x >>= fun r => pure (encodeStep r)
    | .inl _ => StateT.mk fun _ => Part.none) : StateT σ Part.{u} _).run token) = _
  rw [start, Equiv.apply_symm_apply]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  congr 1
  funext p
  exact decode_step p.1 p.2

private theorem finish_wire (op : TwoBlock.Instruction Φ K (Carrier A D)) (k : TyDen K) (token : σ) :
    (model).primitive (.ordered (carriedData (Carrier B K)) (resultData _) (.effect (.finish op)))
      (outputTuple (k, token)) =
      Part.map tagged ((callCase (ε := ε) (m := StateT σ Part.{u}) op k).run token) := by
  change Part.map (decode (ts := results (Carrier A D)))
    (((match TypeModel.coprodEquiv K B (done k) with
    | .inl x => callCase (ε := ε) op x >>= fun r => pure (encodeStep r)
    | .inr _ => StateT.mk fun _ => Part.none) : StateT σ Part.{u} _).run token) = _
  rw [done, Equiv.apply_symm_apply]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  congr 1
  funext p
  exact decode_step p.1 p.2

private noncomputable def innerBody (op : TwoBlock.Instruction Φ B (Carrier B K)) (input : Point σ (Carrier B K)) :
    Part (StepResult σ (Carrier B K)) :=
  (Wiring.innerBody op).1.denoteOpenWith model input PUnit.unit

private theorem inner_body (op : TwoBlock.Instruction Φ B (Carrier B K)) (p : TyDen B × σ) :
    innerBody (ε := ε) op (entryTuple p) =
      Part.map tagged ((callCase (ε := ε) (m := StateT σ Part.{u}) op p.1).run p.2) := by
  unfold innerBody
  simp only [Wiring.innerBody, Wiring.returnStep, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith,
    read_appended, read_cons, read_newest, read_nextRuntime]
  change ((model).primitive (.ordered (carriedData _) (resultData _) (.effect (.inner op))) (entryTuple p)
    >>= fun out : StepResult σ (Carrier B K) => pure (Tuple.cons (out.get .head)
      (point (out.get (.tail .head)) (out.get (.tail (.tail .head)))))) = _
  rw [inner_wire]
  simpa only [step_eta] using bind_pure (Part.map tagged ((callCase (ε := ε) (m := StateT σ Part.{u}) op p.1).run p.2))

/-- A body that agrees on both outcome tag and token induces the same
partial loop observation through the actual numbered θ semantics. -/
private theorem theta_observe (f : TyDen A → StateT σ Part.{u} (TyDen D ⊕ TyDen A))
    (body : Point σ (Carrier A D) → Part (StepResult σ (Carrier A D)))
    (agrees : ∀ p : TyDen A × σ, body (entryTuple p) = Part.map tagged ((f p.1).run p.2))
    (p : TyDen A × σ) :
    iter (stepWith body) (entryTuple p) = Part.map outputTuple ((iter f p.1).run p.2) := by
  rw [Silmaril.Elgot.StateT.run_iter,
    OrderedTheta.iter_boundary _ (stepWith body) entryTuple outputTuple _ p]
  · exact Part.bind_some_eq_map _ _
  · intro x
    unfold stepWith
    rw [Bind.kleisliRight, agrees]
    simp only [Silmaril.Elgot.StateT.body, Part.bind_eq_bind, Part.bind_map, Part.bind_assoc]
    congr 1
    funext result
    rcases result with ⟨result, token⟩
    cases result <;> simp only [Function.comp_apply, Part.pure_eq_some, Part.bind_some] <;> rfl

private noncomputable def outerBody (s : Loop Φ A B K D) (input : Point σ (Carrier A D)) :
    Part (StepResult σ (Carrier A D)) :=
  (Wiring.outerBody s).1.denoteOpenWith model input PUnit.unit

private theorem outer_body (s : Loop Φ A B K D) (p : TyDen A × σ) :
    outerBody (ε := ε) s (entryTuple p) =
      Part.map tagged ((round (ε := ε) (m := StateT σ Part.{u}) s p.1).run p.2) := by
  unfold outerBody
  simp only [Wiring.outerBody, Wiring.returnStep, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith,
    read_appended, read_cons, read_newest, read_nextRuntime]
  change ((model).primitive (.ordered (carriedData (Carrier A D)) (carriedData (Carrier B K))
      (.effect (.enter s.enter))) (entryTuple p) >>= fun entered : Point σ (Carrier B K) =>
    iter (stepWith (innerBody (ε := ε) (σ := σ) s.inner))
        (point (entered.get .head) (entered.get (.tail .head))) >>= fun innerResult : Point σ (Carrier B K) =>
      (model).primitive (.ordered (carriedData (Carrier B K)) (resultData (Carrier A D)) (.effect (.finish s.finish)))
        (point (innerResult.get .head) (innerResult.get (.tail .head))) >>= fun out : StepResult σ (Carrier A D) =>
      pure (Tuple.cons (out.get .head) (point (out.get (.tail .head)) (out.get (.tail (.tail .head)))))) = _
  simp only [step_eta]
  rw [enter_wire]
  simp only [round, bind_assoc, StateT.run_bind, Part.bind_eq_bind, Part.bind_map, Part.map_bind,
    Part.pure_eq_some]
  congr 1
  funext innerInput
  rw [point_eta (entryTuple innerInput), theta_observe (callCase (ε := ε) s.inner) _ (inner_body s.inner)]
  simp only [Part.bind_map]
  congr 1
  funext innerResult
  rw [point_eta (outputTuple innerResult)]
  change ((model).primitive (.ordered (carriedData (Carrier B K)) (resultData (Carrier A D))
    (.effect (.finish s.finish))) (outputTuple innerResult) >>= pure) = _
  rw [bind_pure]
  exact finish_wire (ε := ε) s.finish innerResult.1 innerResult.2

theorem graph_observe (s : Loop Φ A B K D) (a : TyDen A) (token : σ) :
    observe (ε := ε) (graph s) a token =
      Part.map outputTuple ((iter (round (ε := ε) (m := StateT σ Part.{u}) s) a).run token) := by
  unfold observe NestedTheta.Partial.observe graph
  rw [NestedTheta.Term.toTerm_toGraph]
  simp only [Wiring.loop, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith,
    read_appended, read_cons, read_newest, read_nextRuntime]
  change (iter (stepWith (outerBody (ε := ε) s)) (entryTuple (a, token)) >>= fun out =>
    pure (point (out.get .head) (out.get (.tail .head)))) = _
  simp only [point_eta, bind_pure]
  exact theta_observe _ _ (outer_body s) (a, token)

end Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Proofs
