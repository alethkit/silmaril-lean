module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Proofs

open Silmaril.Elgot
open Isotope.LetIter.ProofRelevant.Semantics

universe u
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
variable {X Y : Type u}

def labelStep (head : X → m (X ⊕ Y)) (body : Y → m X) : X ⊕ Y → m (X ⊕ (X ⊕ Y))
  | .inl x => head x >>= fun r => pure (Sum.map id Sum.inr r)
  | .inr y => body y >>= fun x => pure (.inr (.inl x))

private def groupStep {E : Type u} (head : X → m (E ⊕ Y)) (body : Y → m (E ⊕ X)) :
    X ⊕ Y → m ((E ⊕ (X ⊕ Y)) ⊕ (X ⊕ Y))
  | .inl x => head x >>= fun r =>
      match r with
      | .inl out => pure (.inl (.inl out))
      | .inr y => pure (.inr (.inr y))
  | .inr y => body y >>= fun r => pure (.inl (Sum.map id Sum.inl r))

/-- Codiagonal groups a header visit with its optional body visit. -/
theorem collapseWithExits {E : Type u} (head : X → m (E ⊕ Y)) (body : Y → m (E ⊕ X))
    (advance : X → m (E ⊕ X))
    (h : ∀ x, advance x = head x >>= Sum.elim (pure ∘ Sum.inl) body)
    (x : X) :
    iter (labelStepWithExits head body) (.inl x) = iter advance x := by
  let grouped := groupStep head body
  have flat : flattenBody grouped = labelStepWithExits head body := by
    funext p
    cases p with
    | inl x =>
      simp only [flattenBody, Bind.kleisliRight, liftPure, grouped, groupStep,
        labelStepWithExits, bind_assoc]
      congr 1
      funext r
      cases r <;> simp [flatten]
    | inr y =>
      simp [flattenBody, Bind.kleisliRight, liftPure, grouped, groupStep, labelStepWithExits, flatten]
  have atBody (y : Y) :
      iter grouped (.inr y) = body y >>= fun r => pure (Sum.map id Sum.inl r) := by
    rw [congrFun (LawfulElgotMonad.fixpoint grouped) (.inr y)]
    simp [grouped, groupStep]
  have atHead (x : X) : iter grouped (.inl x) = advance x >>= fun r => pure (Sum.map id Sum.inl r) := by
    rw [congrFun (LawfulElgotMonad.fixpoint grouped) (.inl x), h x]
    simp only [grouped, groupStep, bind_assoc]
    congr 1
    funext r
    cases r with
    | inl out => simp [Function.comp_apply, Sum.elim_inl]
    | inr y => exact (pure_bind _ _).trans (atBody y)
  have step : (advance >=> liftPure (Sum.map id Sum.inl)) = (liftPure Sum.inl >=> iter grouped) := by
    funext a
    change (advance a >>= fun r => pure (Sum.map id Sum.inl r)) =
      (pure (Sum.inl a) >>= iter grouped)
    rw [pure_bind]
    exact (atHead a).symm
  have eq := congrFun (LawfulElgotMonad.uniformity advance (iter grouped) Sum.inl step) x
  rw [LawfulElgotMonad.codiagonal, flat] at eq
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] using eq.symm

theorem collapse (head : X → m (X ⊕ Y)) (body : Y → m X)
    (advance : X → m (X ⊕ X))
    (h : ∀ x, advance x = head x >>= fun result =>
      match result with
      | .inl out => pure (.inl out)
      | .inr y => body y >>= fun next => pure (.inr next))
    (x : X) :
    iter (labelStep head body) (.inl x) = iter advance x := by
  let body' : Y → m (X ⊕ X) := fun y => body y >>= fun next => pure (.inr next)
  have eq : labelStep head body = labelStepWithExits head body' := by
    funext p
    cases p <;> simp [labelStep, labelStepWithExits, body']
  rw [eq]
  exact collapseWithExits head body' advance (fun a => by
    rw [h]
    congr 1
    funext result
    cases result <;> rfl) x

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Proofs
