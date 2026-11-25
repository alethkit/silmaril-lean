module

public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Proofs

open Silmaril.Elgot

universe u
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
variable {H B X E : Type u}

def dispatch (header : H → m (E ⊕ B)) (first : B → m X) (last : X → m (E ⊕ H)) :
    H ⊕ (B ⊕ X) → m (E ⊕ (H ⊕ (B ⊕ X)))
  | .inl a => header a >>= fun r => pure (Sum.map id (Sum.inr ∘ Sum.inl) r)
  | .inr (.inl b) => first b >>= fun x => pure (.inr (.inr (.inr x)))
  | .inr (.inr x) => last x >>= fun r => pure (Sum.map id Sum.inl r)

private def inner (header : H → m (E ⊕ B)) (first : B → m X) (last : X → m (E ⊕ H)) :
    H ⊕ (B ⊕ X) → m ((E ⊕ (H ⊕ (B ⊕ X))) ⊕ (H ⊕ (B ⊕ X)))
  | .inl a => header a >>= fun
    | .inl out => pure (.inl (.inl out))
    | .inr b => pure (.inr (.inr (.inl b)))
  | .inr (.inl b) => first b >>= fun x => pure (.inr (.inr (.inr x)))
  | .inr (.inr x) => last x >>= fun r => pure (.inl (Sum.map id Sum.inl r))

/-- Two forward local edges complete inside a single outer header activation. -/
theorem group_chain (header : H → m (E ⊕ B)) (first : B → m X) (last : X → m (E ⊕ H))
    (advance : H → m (E ⊕ H))
    (h : ∀ a, advance a = header a >>= Sum.elim (pure ∘ Sum.inl) (first >=> last))
    (a : H) :
    iter (dispatch header first last) (.inl a) = iter advance a := by
  let g := inner header first last
  have flat : flattenBody g = dispatch header first last := by
    funext p
    rcases p with a | b | x
    · simp only [flattenBody, Bind.kleisliRight, liftPure, g, inner, dispatch, bind_assoc]
      congr 1
      funext r
      cases r <;> simp [flatten]
    · simp [flattenBody, Bind.kleisliRight, liftPure, g, inner, dispatch, flatten]
    · simp [flattenBody, Bind.kleisliRight, liftPure, g, inner, dispatch, flatten]
  have atLast (x : X) : iter g (.inr (.inr x)) =
      last x >>= fun r => pure (Sum.map id Sum.inl r) := by
    rw [congrFun (LawfulElgotMonad.fixpoint g) (.inr (.inr x))]
    simp [g, inner]
  have atFirst (b : B) : iter g (.inr (.inl b)) =
      first b >>= fun x => last x >>= fun r => pure (Sum.map id Sum.inl r) := by
    rw [congrFun (LawfulElgotMonad.fixpoint g) (.inr (.inl b))]
    simp only [g, inner, bind_assoc, pure_bind]
    congr 1
    funext x
    exact atLast x
  have atHeader (a : H) : iter g (.inl a) =
      advance a >>= fun r => pure (Sum.map id Sum.inl r) := by
    rw [congrFun (LawfulElgotMonad.fixpoint g) (.inl a), h a]
    simp only [g, inner, bind_assoc]
    congr 1
    funext r
    cases r with
    | inl out => simp [Function.comp_apply, Sum.elim_inl]
    | inr b =>
      rw [pure_bind]
      exact (atFirst b).trans (by simp [Bind.kleisliRight])
  have step : (advance >=> liftPure (Sum.map id Sum.inl)) = (liftPure Sum.inl >=> iter g) := by
    funext a
    change (advance a >>= fun r => pure (Sum.map id Sum.inl r)) = (pure (Sum.inl a) >>= iter g)
    rw [pure_bind]
    exact (atHeader a).symm
  have eq := congrFun (LawfulElgotMonad.uniformity advance (iter g) Sum.inl step) a
  rw [LawfulElgotMonad.codiagonal, flat] at eq
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] using eq.symm

end Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Proofs
