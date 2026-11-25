module

public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Model.Defs

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Proofs

open Silmaril.Elgot

universe u
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

/-- Change the pure representation of both boundaries without changing when
the body computation executes. -/
theorem iter_boundary {A B X Y : Type u} (f : A → m (B ⊕ A)) (g : X → m (Y ⊕ X))
    (input : A → X) (output : B → Y)
    (comm : ∀ x, g (input x) = f x >>= fun result => pure (Sum.map output input result))
    (x : A) : iter g (input x) = iter f x >>= fun b => pure (output b) := by
  have step : (mapReturn f (liftPure output) >=> liftPure (Sum.map id input)) =
      (liftPure input >=> g) := by
    funext a
    change mapReturn f (liftPure output) a >>= (fun result => pure (Sum.map id input result)) =
      (pure (input a) >>= g)
    rw [pure_bind, comm]
    simp only [mapReturn, liftPure, Function.comp_apply, bind_assoc]
    congr 1
    funext result
    cases result <;> simp
  have eq := congrFun (LawfulElgotMonad.uniformity _ _ _ step) x
  rw [← LawfulElgotMonad.naturality] at eq
  change (iter f x >>= fun b => pure (output b)) = (pure (input x) >>= iter g) at eq
  simpa only [pure_bind] using eq.symm

end Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Proofs
