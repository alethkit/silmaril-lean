module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Proofs

open CategoryTheory Silmaril.Elgot
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LetIter.ProofRelevant.Semantics
open OrderedTheta (pack unpack packChoice exit ValueTuple ResultTuple)
open OrderedRuntime.Structured
open NestedTheta (stepWith)

@[simp] private theorem fin_cases_one {U : Fin 2 → Sort*} (z : U 0) (s : (i : Fin 1) → U i.succ) :
    Fin.cases (motive := U) z s (1 : Fin 2) = s 0 :=
  Fin.cases_succ (motive := U) (0 : Fin 1)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [_root_.Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A B : τ}

set_option backward.isDefEq.respectTransparency false

omit [LawfulElgotMonad m] in
private theorem body_computes (s : Blocks Φ A B) (a : TyDen A) :
    (thetaBody s).denoteOpenWith (model (ε := ε) (m := m)) (pack a) PUnit.unit =
      round (ε := ε) s a >>= fun result => pure (packChoice result) := by
  simp only [thetaBody, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith, model, OrderedRuntime.Structured.Model.step, orderedModel,
    Wires.read, Tuple.map, Tuple.get, Locals.snoc, Locals.get, pack, round, bind_assoc, pure_bind]
  congr 1
  funext result
  cases result <;> simp [headerResult, arm, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith,
    OrderedRuntime.Structured.Model.step, Wires.read, Tuple.map, Tuple.get, Locals.snoc, Locals.get,
    packChoice, loopResult, pack]
  · rename_i x
    change (pure (loopResult 0 (Sum.elim id (fun _ => a)
      (TypeModel.coprodEquiv A B ((TypeModel.coprodEquiv A B).symm (.inl x))))) : m _) =
        pure (loopResult 0 x)
    rw [Equiv.apply_symm_apply]
    rfl
  · rename_i y
    change (fun zs : ResultTuple A => Tuple.cons (zs.get .head) (.cons (zs.get (.tail .head)) .nil)) <$>
      (match TypeModel.coprodEquiv A B ((TypeModel.coprodEquiv A B).symm (.inr y)) with
       | .inl _ => pure (loopResult 1 a)
       | .inr b => loopResult 1 <$> call (ε := ε) s.body b) =
      loopResult 1 <$> call (ε := ε) s.body y
    simp only [Equiv.apply_symm_apply, Functor.map_map]
    rfl

omit [LawfulElgotMonad m] in
private theorem step_computes (s : Blocks Φ A B) (a : TyDen A) :
    stepWith (fun input => (thetaBody s).denoteOpenWith (model (ε := ε) (m := m)) input PUnit.unit)
        (pack a) =
      round (ε := ε) s a >>= fun result => pure (Sum.map pack pack result) := by
  unfold stepWith
  rw [Bind.kleisliRight, body_computes, bind_assoc]
  congr 1
  funext result
  cases result <;> simp only [pure_bind] <;> rfl

theorem graph_iterates (s : Blocks Φ A B) (env : Env [A]) :
    denote (ε := ε) (m := m) (graph s) env =
      iter (round (ε := ε) s) env.2 >>= fun a => pure (exit a) := by
  let body := fun input : ValueTuple A =>
    (thetaBody s).denoteOpenWith (model (ε := ε) (m := m)) input PUnit.unit
  let step := stepWith body
  have normalized : denote (ε := ε) (m := m) (graph s) env =
      iter step (pack env.2) >>= fun result => pure (exit (unpack result)) := by
    unfold denote graph
    rw [NestedTheta.Term.toTerm_toGraph]
    change (loopTerm s).denoteOpenWith (model (ε := ε) (m := m)) (pack env.2) PUnit.unit >>= _ = _
    simp only [loopTerm, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith, bind_assoc, pure_bind]
    congr 1
  rw [normalized, OrderedTheta.iter_boundary (round (ε := ε) s) step pack pack
    (step_computes s) env.2, bind_assoc]
  simp only [pure_bind]
  rfl

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Proofs
