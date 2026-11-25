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

private def groupStep (head : X → m (X ⊕ Y)) (body : Y → m X) :
    X ⊕ Y → m ((X ⊕ (X ⊕ Y)) ⊕ (X ⊕ Y))
  | .inl x => head x >>= fun r =>
      match r with
      | .inl out => pure (.inl (.inl out))
      | .inr y => pure (.inr (.inr y))
  | .inr y => body y >>= fun x => pure (.inl (.inr (.inl x)))

/-- One inner iteration dispatches the body on entry to its label. Codiagonal
recovers the original interleaved CFG iteration. -/
theorem collapse (head : X → m (X ⊕ Y)) (body : Y → m X)
    (advance : X → m (X ⊕ X))
    (h : ∀ x, advance x = head x >>= fun result =>
      match result with
      | .inl out => pure (.inl out)
      | .inr y => body y >>= fun next => pure (.inr next))
    (x : X) :
    iter (labelStep head body) (.inl x) = iter advance x := by
  let grouped := groupStep head body
  have flat : flattenBody grouped = labelStep head body := by
    funext p
    cases p with
    | inl x =>
      simp only [flattenBody, Bind.kleisliRight, liftPure, grouped, groupStep,
        labelStep, bind_assoc]
      congr 1
      funext r
      cases r <;> simp [flatten]
    | inr y =>
      simp [flattenBody, Bind.kleisliRight, liftPure, grouped, groupStep, labelStep, flatten]
  have atBody (y : Y) : iter grouped (.inr y) = body y >>= fun a => pure (.inr (.inl a)) := by
    rw [congrFun (LawfulElgotMonad.fixpoint grouped) (.inr y)]
    simp [grouped, groupStep]
  have atHead (x : X) : iter grouped (.inl x) = advance x >>= fun r => pure (Sum.map id Sum.inl r) := by
    rw [congrFun (LawfulElgotMonad.fixpoint grouped) (.inl x), h x]
    simp only [grouped, groupStep, bind_assoc]
    congr 1
    funext r
    cases r with
    | inl out => simp only [pure_bind]; rfl
    | inr y =>
      simp only [pure_bind]
      change iter grouped (.inr y) =
        ((body y >>= fun a => pure (Sum.inr a)) >>= fun r => pure (Sum.map id Sum.inl r))
      rw [atBody, bind_assoc]
      simp only [pure_bind]
      rfl
  have step : (advance >=> liftPure (Sum.map id Sum.inl)) = (liftPure Sum.inl >=> iter grouped) := by
    funext a
    change (advance a >>= fun r => pure (Sum.map id Sum.inl r)) =
      (pure (Sum.inl a) >>= iter grouped)
    rw [pure_bind]
    exact (atHead a).symm
  have eq := congrFun (LawfulElgotMonad.uniformity advance (iter grouped) Sum.inl step) x
  rw [LawfulElgotMonad.codiagonal, flat] at eq
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] using eq.symm

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Proofs
