module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Source
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Body

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen Env)
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (carried carriedData resultData results point pack)
open OrderedRuntime.Structured (RuntimeValues Threaded encode decode read_cons read_appended)
open ExplicitRuntime.Proofs (eval eval_primitive eval_choice eval_finish read_newest read_nextRuntime)
open TwoBlock.TwoExit (Carrier ExitCode callCase enter finish exitLabel)
open TwoBlock.TwoExit.ExplicitRuntime (exitPayload)
open NestedTheta (Term Kind Node)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A L B K E D X : τ}

private abbrev Point (X : τ) := Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (carried X))

private theorem repack (p : Point (σ := σ) X) :
    point (p.get .head) (p.get (.tail .head)) = p := by
  cases p with
  | cons value tail =>
    cases tail with
    | cons token tail => cases tail; rfl

private def classify (s : Guarded Φ A L B K E D) (x : TyDen A) (initial : σ) :=
  (ExplicitRuntime.wireModel (ε := ε)).primitive
    (.ordered (carriedData A) (resultData (Carrier L E D)) (.effect (.acyclic (.classify .direct s.gate))))
    (point x initial)

private def gateResult (r : (TyDen (ExitCode E D) ⊕ TyDen L) × σ) :
    Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (results (Carrier L E D))) :=
  decode (ExplicitRuntime.choiceData r.1, r.2)

private theorem classify_eq (s : Guarded Φ A L B K E D) (x : TyDen A) (initial : σ) :
    classify (ε := ε) s x initial =
      Part.map gateResult ((callCase (ε := ε) (m := StateT σ Part.{u}) s.gate x).run initial) := by
  change Part.map decode ((callCase (ε := ε) s.gate x >>= fun r =>
    (pure (ExplicitRuntime.choiceData r) : StateT σ Part.{u} _)).run initial) = _
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map, Function.comp_def]
  rfl

private theorem graph_eval (s : Guarded Φ A L B K E D) (x : TyDen A) (initial : σ) :
    observe (ε := ε) (graph s) x initial =
      eval (ε := ε) (Wiring.openCode s) (point x initial) PUnit.unit :=
  congrArg (fun t => t.denoteOpenWith (ExplicitRuntime.wireModel (ε := ε) (σ := σ))
    (point x initial) PUnit.unit) (NestedTheta.Term.toTerm_toGraph (Wiring.code s).1)

private theorem loop_eval (s : Guarded Φ A L B K E D) (x : TyDen L) (token : σ) :
    eval (ε := ε) (Wiring.arm s) (point (enter x) token) PUnit.unit =
      ExplicitRuntime.observe (ε := ε) (ExplicitRuntime.graph s.loop) x token :=
  (congrArg (fun t => t.denoteOpenWith (ExplicitRuntime.wireModel (ε := ε) (σ := σ))
    (point (enter x) token) PUnit.unit) (NestedTheta.Term.toTerm_toGraph (ExplicitRuntime.Wiring.loop s.loop).1)).symm

private theorem point_exit (ext : TyDen (ExitCode E D)) (token : σ) :
    point ((TypeModel.coprodEquiv (ExitCode E D) L).symm (.inl ext)) token =
      ExplicitRuntime.exitTuple (A := L) (exitLabel (TypeModel.coprodEquiv E D ext), token) := by
  unfold ExplicitRuntime.exitTuple finish
  have label : exitPayload (exitLabel (TypeModel.coprodEquiv E D ext)) = TypeModel.coprodEquiv E D ext := by
    cases TypeModel.coprodEquiv E D ext <;> rfl
  rw [label, Equiv.symm_apply_apply]

theorem graph_observe (s : Guarded Φ A L B K E D) (x : TyDen A) (initial : σ) :
    observe (ε := ε) (graph s) x initial =
      Part.map (ExplicitRuntime.exitTuple (A := L))
        (((gateAction (ε := ε) s x : StateT σ Part.{u} _) >>= fun
          | .inl external => pure external
          | .inr header => Silmaril.Elgot.iter
            (ExplicitRuntime.round (ε := ε) (m := StateT σ Part.{u}) s.loop) header).run initial) := by
  rw [graph_eval]
  simp only [Wiring.openCode, eval_primitive, Part.bind_eq_bind]
  change (classify (ε := ε) s x initial).bind _ = _
  rw [classify_eq, Part.bind_map, StateT.run_bind, Part.bind_eq_bind, Part.map_bind]
  unfold gateAction
  rw [StateT.run_bind]
  simp only [StateT.run_pure, Part.bind_eq_bind, Part.bind_assoc, Part.pure_eq_some, Part.bind_some]
  congr 1
  funext returned
  rcases returned with ⟨selected, token⟩
  simp only [eval_choice, read_newest, read_nextRuntime, read_appended, read_cons, Part.bind_eq_bind]
  cases selected with
  | inl exited =>
    change (Part.some (point ((TypeModel.coprodEquiv (ExitCode E D) L).symm (.inl exited)) token)).bind
      (fun q : Point (σ := σ) (Carrier L E D) => Part.some (point (q.get .head) (q.get (.tail .head)))) =
      Part.map (ExplicitRuntime.exitTuple (A := L))
        (Part.some (exitLabel (TypeModel.coprodEquiv E D exited), token))
    rw [Part.bind_some, repack, Part.map_some, point_exit]
  | inr header =>
    change (eval (ε := ε) (Wiring.arm s) (point (enter header) token) PUnit.unit).bind
      (fun q : Point (σ := σ) (Carrier L E D) => Part.some (point (q.get .head) (q.get (.tail .head)))) = _
    simp only [repack, Part.bind_some_right]
    exact (loop_eval s header token).trans (ExplicitRuntime.graph_observe s.loop header token)


theorem region_observe (s : Guarded Φ A L B K E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) (graph s) env.2 initial =
      Part.map (ExplicitRuntime.exitTuple (A := L))
        ((Isotope.LambdaSSA.Semantics.Monadic.Region.denote (ε := ε) (m := StateT σ Part.{u}) (regionTyping s) env).run initial) := by
  rw [graph_observe, region_gate s coherent env]
  simp only [StateT.run_bind, Part.bind_eq_bind, Part.map_bind]
  congr 1
  funext result
  rcases result with ⟨branch, token⟩
  cases branch with
  | inl => rfl
  | inr x =>
    exact (ExplicitRuntime.graph_observe (ε := ε) s.loop x token).symm.trans
      ((ExplicitRuntime.Related.loop s.loop).region_observe coherent (PUnit.unit, x) token)

theorem returns_of_observe (g : Graph Φ A L E D) (a : TyDen A) (initial final : σ)
    (label : LabelDen [E,D]) (observation : Part (LabelDen [E,D] × σ))
    (agrees : observe (ε := ε) g a initial = Part.map (ExplicitRuntime.exitTuple (A := L)) observation) :
    returns (ε := ε) g a initial label final ↔ observation = Part.some (label, final) := by
  unfold returns
  rw [← NestedTheta.Partial.observe_eq_some]
  change (observe (ε := ε) g a initial = Part.some (ExplicitRuntime.exitTuple (A := L) (label, final))) ↔ _
  rw [agrees, Part.eq_some_iff, Part.mem_map_iff, Part.eq_some_iff]
  simp only [ExplicitRuntime.exitTuple_injective.eq_iff, exists_eq_right]

theorem map_none_iff {X Y : Type*} (f : X → Y) (v : Part X) :
    Part.map f v = Part.none ↔ v = Part.none := by
  rw [Part.eq_none_iff', Part.eq_none_iff']
  rfl

open NestedTheta.ExplicitRuntime (EntryChecked boundaryResult)
open NestedTheta.ExplicitRuntime.Partial (observeErased observe_eq)

theorem erased_of_observe (g : Graph Φ A L E D)
    (checked : EntryChecked (a := carriedData A) (b := carriedData (Carrier L E D)) g.toTerm)
    (x : TyDen A) (initial : σ) (observation : Part (LabelDen [E,D] × σ))
    (agrees : observe (ε := ε) g x initial = Part.map (ExplicitRuntime.exitTuple (A := L)) observation) :
    observeErased (ExplicitRuntime.orderedModel (ε := ε) (σ := σ)) g checked (point x initial) =
      Part.map (boundaryResult ∘ ExplicitRuntime.exitTuple (A := L)) observation := by
  let erase : Point (σ := σ) (Carrier L E D) →
      NestedTheta.OrderedState.Configuration (TyDen (τ := τ)) σ (Threaded (carried (Carrier L E D))) :=
    boundaryResult
  have bridge : _ = Part.map erase (observe (ε := ε) g x initial) :=
    (observe_eq (ExplicitRuntime.orderedModel (ε := ε) (σ := σ)) g checked (point x initial)).symm
  exact bridge.trans ((congrArg (Part.map erase) agrees).trans (Part.map_map erase _ _))

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Proofs
