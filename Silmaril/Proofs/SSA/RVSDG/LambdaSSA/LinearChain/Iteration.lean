module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Model.Defs

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Proofs

open Silmaril.Elgot
open Isotope.LetIter.ProofRelevant.Semantics
open TwoBlock.TwoExit (callCase)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A B D : τ} {tail : List τ} {I E : Type u}
set_option backward.isDefEq.respectTransparency false

/-- Only forward edges are fed back by the inner iteration. -/
def innerBody (resume : TyDen A → I) (leave : TyDen D → E) :
    {B : τ} → {tail : List τ} → Body Φ A D B tail →
    (∀ i : Fin (B :: tail).length, TyDen ((B :: tail).get i) → I) →
    ∀ i : Fin (B :: tail).length, TyDen ((B :: tail).get i) → m ((E ⊕ I) ⊕ I)
  | _, _, .last op, _, i =>
    Fin.cases (motive := fun j => TyDen ([_].get j) → m ((E ⊕ I) ⊕ I))
      (fun b => callCase (ε := ε) op b >>= fun r => pure (.inl (Sum.map leave resume r)))
      (fun j => j.elim0) i
  | _, _, .next op rest, locate, i =>
    Fin.cases (motive := fun j => TyDen ((_ :: _ :: _).get j) → m ((E ⊕ I) ⊕ I))
      (fun b => TwoBlock.call (ε := ε) op b >>= fun x => pure (.inr (locate (0 : Fin _).succ x)))
      (innerBody resume leave rest (fun j => locate j.succ)) i

theorem iter_body (resume : TyDen A → I) (leave : TyDen D → E)
    (body : Body Φ A D B tail)
    (locate : ∀ i : Fin (B :: tail).length, TyDen ((B :: tail).get i) → I)
    (f : I → m ((E ⊕ I) ⊕ I))
    (steps : ∀ i x, f (locate i x) = innerBody (ε := ε) resume leave body locate i x)
    (b : TyDen B) :
    iter f (locate 0 b) = body.fold (ε := ε) b >>= fun r => pure (Sum.map leave resume r) := by
  induction body with
  | last op =>
    rw [congrFun (LawfulElgotMonad.fixpoint f) (locate 0 b), steps 0 b]
    simp [innerBody, Body.fold]
  | next op rest ih =>
    rw [congrFun (LawfulElgotMonad.fixpoint f) (locate 0 b), steps 0 b]
    simp only [innerBody, Fin.cases_zero, Body.fold, bind_assoc, pure_bind]
    congr 1
    funext x
    exact ih (fun j => locate j.succ) (fun j a =>
      (steps j.succ a).trans (by rw [innerBody, Fin.cases_succ])) x

omit [InstructionModel Φ τ ε m] in
theorem close_grouped {H : Type u} (enter : H → I)
    (inner : I → m ((E ⊕ I) ⊕ I)) (round : H → m (E ⊕ H))
    (atHeader : ∀ a, iter inner (enter a) = round a >>= fun r => pure (Sum.map id enter r))
    (a : H) : iter (flattenBody inner) (enter a) = iter round a := by
  have h : (round >=> liftPure (Sum.map id enter)) = (liftPure enter >=> iter inner) := by
    funext a
    change (round a >>= fun r => pure (Sum.map id enter r)) =
      (pure (enter a) >>= iter inner)
    rw [pure_bind]
    exact (atHeader a).symm
  have result := congrFun (LawfulElgotMonad.uniformity round (iter inner) enter h) a
  rw [LawfulElgotMonad.codiagonal] at result
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] using result.symm

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Proofs
