module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Proofs

open CategoryTheory Silmaril.Elgot
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LetIter.ProofRelevant.Semantics
open OrderedTheta (pack unpack packChoice ValueTuple ResultTuple)
open OrderedRuntime.Structured
open NestedTheta (stepWith)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A B C D : τ}

set_option backward.isDefEq.respectTransparency false

@[simp] private theorem fin_cases_one {F : Fin 2 → Sort*} (z : F 0) (s : (j : Fin 1) → F j.succ) :
    Fin.cases (motive := F) z s (1 : Fin 2) = s 0 :=
  Fin.cases_succ (motive := F) (0 : Fin 1)

private def rewire (zs : ResultTuple (Carrier A C D)) : ResultTuple (Carrier A C D) :=
  .cons (zs.get .head) (.cons (zs.get (.tail .head)) .nil)

omit [LawfulElgotMonad m] in
private theorem body_computes (s : Blocks Φ A B C D) (a : TyDen A) :
    (thetaBody s).denoteOpenWith (model (ε := ε) (m := m)) (pack (enter a)) PUnit.unit =
      round (ε := ε) s a >>= fun result => pure (packChoice (Sum.map finish enter result)) := by
  simp only [thetaBody, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith, model,
    Model.step, orderedModel, Wires.read, Tuple.map, Tuple.get, Locals.snoc, Locals.get, pack,
    enter, Equiv.apply_symm_apply, round, bind_assoc, pure_bind]
  congr 1
  funext result
  cases result with
  | inl c =>
    simp only [Sum.map_inl, routeResult, Fin.cases_zero, fin_cases_one, Tuple.get,
      arm, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith, Model.step,
      Wires.read, Tuple.map, Locals.snoc, Locals.get,
      pure_bind, finish]
    change (pure (rewire (match TypeModel.coprodEquiv (ExitCode C D) B
      ((TypeModel.coprodEquiv (ExitCode C D) B).symm
        (.inl ((TypeModel.coprodEquiv C D).symm (.inl c)))) with
      | .inl out => packChoice (.inl ((TypeModel.coprodEquiv (ExitCode C D) A).symm (.inl out)))
      | .inr _ => packChoice (.inr ((TypeModel.coprodEquiv (ExitCode C D) A).symm (.inr a))))) : m _) = _
    rw [Equiv.apply_symm_apply]
    rfl
  | inr b =>
    simp only [Sum.map_inr, id_eq, routeResult, Fin.cases_zero, fin_cases_one, Tuple.get,
      arm, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith, Model.step,
      Wires.read, Tuple.map, Locals.snoc, Locals.get,
      bind_assoc, pure_bind]
    change ((match TypeModel.coprodEquiv (ExitCode C D) B
        ((TypeModel.coprodEquiv (ExitCode C D) B).symm (.inr b)) with
      | .inl out => pure (packChoice (.inl ((TypeModel.coprodEquiv (ExitCode C D) A).symm (.inl out))))
      | .inr b => callCase (ε := ε) s.body b >>= fun result =>
          pure (packChoice (Sum.map (fun d => finish (A := A) (C := C) (.inr d)) enter result))) >>=
      fun result => pure (rewire (rewire result))) = _
    rw [Equiv.apply_symm_apply, bind_assoc]
    simp only [pure_bind]
    congr 1
    funext result
    cases result <;> simp only [pure_bind] <;> rfl

omit [LawfulElgotMonad m] in
private theorem step_computes (s : Blocks Φ A B C D) (a : TyDen A) :
    stepWith (fun input => (thetaBody s).denoteOpenWith (model (ε := ε) (m := m)) input PUnit.unit)
        (pack (enter a)) =
      round (ε := ε) s a >>= fun result => pure (Sum.map (pack ∘ finish) (pack ∘ enter) result) := by
  unfold stepWith
  rw [Bind.kleisliRight, body_computes, bind_assoc]
  congr 1
  funext result
  cases result <;> simp only [pure_bind] <;> rfl

theorem carrier_iterates (s : Blocks Φ A B C D) (a : TyDen A) :
    denoteCarrier (ε := ε) (m := m) (graph s) a =
      iter (round (ε := ε) s) a >>= fun out => pure (finish out) := by
  let body := fun input : ValueTuple (Carrier A C D) =>
    (thetaBody s).denoteOpenWith (model (ε := ε) (m := m)) input PUnit.unit
  let step := stepWith body
  have normalized : denoteCarrier (ε := ε) (m := m) (graph s) a =
      iter step (pack (enter (C := C) (D := D) a)) >>= fun result => pure (unpack result) := by
    unfold denoteCarrier graph
    rw [NestedTheta.Term.toTerm_toGraph]
    change (loopTerm s).denoteOpenWith (model (ε := ε) (m := m)) (pack (enter a)) PUnit.unit >>= _ = _
    simp only [loopTerm, NestedTheta.Term.denoteOpenWith, NestedTheta.Kind.denoteWith, bind_assoc, pure_bind]
    congr 1
  have iterate := OrderedTheta.iter_boundary (round (ε := ε) s) step (pack ∘ enter) (pack ∘ finish)
    (step_computes s) a
  simp only [Function.comp_apply] at iterate
  rw [normalized, iterate, bind_assoc]
  simp only [pure_bind]
  rfl

omit [LawfulMonad m] [LawfulElgotMonad m] in
private theorem decode_finish (out : TyDen C ⊕ TyDen D) :
    decode (A := A) (m := m) (finish out) = pure (exitLabel out) := by
  simp only [decode, finish, Equiv.apply_symm_apply]

theorem graph_iterates (s : Blocks Φ A B C D) (env : Env [A]) :
    denote (ε := ε) (m := m) (graph s) env =
      iter (round (ε := ε) s) env.2 >>= fun out => pure (exitLabel out) := by
  rw [denote, carrier_iterates, bind_assoc]
  simp only [pure_bind, decode_finish]

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Proofs
