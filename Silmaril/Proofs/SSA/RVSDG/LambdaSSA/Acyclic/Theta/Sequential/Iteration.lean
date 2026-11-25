module

public import Silmaril.Semantics.Elgot.Thms

/-! # Two Elgot phases with only a forward handoff -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Proofs

open Silmaril.Elgot

universe u
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
variable {I J M E : Type u}

private def grouped (first : I → m (M ⊕ I)) (second : J → m (E ⊕ J)) (enter : M → J) :
    (I ⊕ J) → m ((E ⊕ (I ⊕ J)) ⊕ (I ⊕ J))
  | .inl i => first i >>= fun result => pure (Sum.map (Sum.inr ∘ Sum.inr ∘ enter) Sum.inl result)
  | .inr j => second j >>= fun result => pure (Sum.map Sum.inl Sum.inr result)

private theorem left_iter (first : I → m (M ⊕ I)) (second : J → m (E ⊕ J)) (enter : M → J)
    (i : I) : iter (grouped first second enter) (.inl i) =
      iter first i >>= fun mid => pure (.inr (.inr (enter mid))) := by
  let ret : M → E ⊕ (I ⊕ J) := Sum.inr ∘ Sum.inr ∘ enter
  have commute : (mapReturn first (pure ∘ ret) >=> liftPure (Sum.map id Sum.inl)) =
      (liftPure Sum.inl >=> grouped first second enter) := by
    funext x
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, mapReturn, pure_bind, bind_assoc, grouped]
    congr 1
    funext result
    cases result <;> simp [ret]
  have natural := congrFun (LawfulElgotMonad.naturality first (pure ∘ ret)) i
  have uniform := congrFun (LawfulElgotMonad.uniformity _ _ _ commute) i
  rw [← natural] at uniform
  simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] at uniform
  exact uniform.symm

private theorem right_iter (first : I → m (M ⊕ I)) (second : J → m (E ⊕ J)) (enter : M → J)
    (j : J) : iter (grouped first second enter) (.inr j) =
      iter second j >>= fun out => pure (.inl out) := by
  let ret : E → E ⊕ (I ⊕ J) := Sum.inl
  have commute : (mapReturn second (pure ∘ ret) >=> liftPure (Sum.map id Sum.inr)) =
      (liftPure Sum.inr >=> grouped first second enter) := by
    funext x
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, mapReturn, pure_bind, bind_assoc, grouped]
    congr 1
    funext result
    cases result <;> simp [ret]
  have natural := congrFun (LawfulElgotMonad.naturality second (pure ∘ ret)) j
  have uniform := congrFun (LawfulElgotMonad.uniformity _ _ _ commute) j
  rw [← natural] at uniform
  simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] at uniform
  exact uniform.symm

theorem iter_sequential (first : I → m (M ⊕ I)) (second : J → m (E ⊕ J)) (enter : M → J)
    (flat : I ⊕ J → m (E ⊕ (I ⊕ J)))
    (left : ∀ i, flat (.inl i) = first i >>= fun r =>
      pure (.inr (Sum.elim (Sum.inr ∘ enter) Sum.inl r)))
    (right : ∀ j, flat (.inr j) = second j >>= fun r => pure (Sum.map id Sum.inr r))
    (i : I) : iter flat (.inl i) = iter first i >>= fun mid => iter second (enter mid) := by
  have flatten : flat = flattenBody (grouped first second enter) := by
    funext p
    cases p with
    | inl i =>
      rw [left]
      simp only [flattenBody, Bind.kleisliRight, liftPure, grouped, bind_assoc]
      congr 1
      funext r
      cases r <;> simp [Silmaril.Elgot.flatten]
    | inr j =>
      rw [right]
      simp only [flattenBody, Bind.kleisliRight, liftPure, grouped, bind_assoc]
      congr 1
      funext r
      cases r <;> simp [Silmaril.Elgot.flatten]
  rw [flatten, ← LawfulElgotMonad.codiagonal]
  rw [congrFun (LawfulElgotMonad.fixpoint (iter (grouped first second enter))) (.inl i),
    left_iter, bind_assoc]
  congr 1
  funext mid
  rw [pure_bind]
  change iter (iter (grouped first second enter)) (.inr (enter mid)) = _
  rw [congrFun (LawfulElgotMonad.fixpoint (iter (grouped first second enter))) (.inr (enter mid)),
    right_iter, bind_assoc]
  simp

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Proofs
