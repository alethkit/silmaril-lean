module

public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.OrderedTheta.Iteration

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Proofs

open CategoryTheory
open Silmaril.Elgot Isotope.LetIter.ProofRelevant.Semantics
open OrderedRuntime.Structured

universe u

variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m]
variable {A : τ}

set_option backward.isDefEq.respectTransparency false

private theorem body_run (f : Steps (τ := τ) Φ m) (s : Step Φ A) (a : TyDen A) :
    OrderedRuntime.Structured.Theta.bodyComputation.{u,u,u} (orderedModel f) (graph s) (graphChecked s) (pack a) =
      packChoice <$> f s a := by
  change denoteGraph.{u,u,u} (orderedModel f) (body s).toGraph (bodyChecked s).collect (pack a) = _
  rw [denote_toGraph]
  simp only [Checked.denote, bodyChecked, Checked.eval, inputWires, outputWires,
    OrderedRuntime.Structured.Model.step, orderedModel, Wires.read, withRuntime]
  simp only [Tuple.map, pack, withRuntime, Tuple.get, Locals.get, Locals.snoc, Fin.cases_zero]
  refine Eq.trans ?_ (bind_pure (packChoice <$> f s a))
  apply congrArg (fun k => (packChoice <$> f s a) >>= k)
  funext output
  cases output with
  | cons tag rest =>
    cases rest with
    | cons value tail =>
      cases tail
      rfl

theorem graph_step (f : Steps (τ := τ) Φ m) (s : Step Φ A) (a : TyDen A) :
    OrderedRuntime.Structured.Theta.step.{u,u,u} (orderedModel f) (graph s) (graphChecked s) (pack a) =
      f s a >>= fun z => pure (Sum.map pack pack z) := by
  unfold OrderedRuntime.Structured.Theta.step
  rw [body_run]
  change ((packChoice <$> f s a) >>= fun z => pure (OrderedRuntime.Structured.Theta.route.{u,u} z)) = _
  rw [bind_map_left]
  congr 1
  funext z
  cases z <;> rfl

variable [Iterate m] [LawfulElgotMonad m]

theorem graph_iter (f : Steps (τ := τ) Φ m) (s : Step Φ A) (a : TyDen A) :
    (OrderedRuntime.Structured.Theta.denote.{u,u,u} (orderedModel f) (graph s) (graphChecked s)).of (pack a) =
      iter (f s) a >>= fun b => pure (pack b) := by
  change (OrderedRuntime.Structured.Theta.close
    (OrderedRuntime.Structured.Theta.step.{u,u,u} (orderedModel f) (graph s) (graphChecked s))).of (pack a) = _
  rw [OrderedRuntime.Structured.Theta.close_of]
  exact iter_boundary _ _ pack pack (graph_step f s) a

section State

variable {σ : Type u}

private theorem total_step (f : Steps (τ := τ) Φ (StateM σ)) (s : Step Φ A) :
    OrderedRuntime.Structured.Theta.totalStep.{u,u,u} (orderedModel f) (graph s) (graphChecked s) =
    OrderedRuntime.Structured.Theta.step.{u,u,u} (orderedModel (liftState f)) (graph s) (graphChecked s) := by
  funext payload
  cases payload with
  | cons a tail =>
    cases tail
    change TyDen A at a
    change OrderedRuntime.Structured.Theta.totalStep.{u,u,u} (orderedModel f)
      (graph s) (graphChecked s) (pack a) = OrderedRuntime.Structured.Theta.step.{u,u,u}
        (orderedModel (liftState f)) (graph s) (graphChecked s) (pack a)
    rw [graph_step (liftState f) s a]
    unfold OrderedRuntime.Structured.Theta.totalStep
    rw [body_run]
    apply StateT.ext
    intro state
    simp only [liftState, StateT.run]
    change Part.some (OrderedRuntime.Structured.Theta.route.{u,u}
        (packChoice ((f s a).run state).1), ((f s a).run state).2) =
      (Part.some ((f s a).run state)).bind (fun z =>
        Part.some (Sum.map pack pack z.1, z.2))
    rw [Part.bind_some]
    cases ((f s a).run state).1 <;> rfl

theorem state_observation (f : Steps (τ := τ) Φ (StateM σ))
    (s : Step Φ A) (a : TyDen A) (state : σ) :
    (iter (liftState f s) a).run state =
      observe <$> OrderedRuntime.Structured.Theta.denoteTotal.{u,u,u}
        (orderedModel f) (graph s) (graphChecked s) (point a state) := by
  unfold OrderedRuntime.Structured.Theta.denoteTotal
  change (iter (liftState f s) a).run state = observe <$> (decode.{u,u} <$>
    ((OrderedRuntime.Structured.Theta.close
      (OrderedRuntime.Structured.Theta.totalStep.{u,u,u} (orderedModel f)
        (graph s) (graphChecked s))).of (pack a)).run state)
  rw [total_step]
  change _ = observe <$> (decode.{u,u} <$>
    ((OrderedRuntime.Structured.Theta.denote.{u,u,u} (orderedModel (liftState f))
      (graph s) (graphChecked s)).of (pack a)).run state)
  rw [graph_iter]
  rw [LawfulMonad.bind_pure_comp, StateT.run_map]
  simp only [Functor.map_map]
  have maps : (fun p : TyDen A × σ => observe (decode.{u,u} (pack p.1, p.2))) = id := by
    funext p
    simp only [observe, encode_decode.{u,u}]
    rfl
  rw [maps, id_map]

end State

end Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Proofs
