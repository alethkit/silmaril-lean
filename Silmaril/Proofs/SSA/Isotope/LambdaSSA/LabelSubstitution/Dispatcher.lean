module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Defs

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Semantics.Monadic

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {m : Type v → Type v} [Monad m] [LawfulMonad m]
  {Γ : VCtx τ} {L K : LCtx τ}

private theorem liftLabels_split (k : Continuation (m := m) Γ L K)
    (R : LCtx τ) (ρ : Env Γ) (x : LabelDen (R ++ L)) :
    (k.liftLabels R ρ x >>= (pure ∘ LabelValue.appendSplit R K)) =
      Sum.elim (fun y => k ρ y >>= (pure ∘ Sum.inl)) (pure ∘ Sum.inr)
        (LabelValue.appendSplit R L x) := by
  induction R with
  | nil => rfl
  | cons A R ih =>
    change LabelDen (A :: (R ++ L)) at x
    rcases show TyDen A ⊕ LabelDen (R ++ L) from x with a | x
    · simp [Continuation.liftLabels, LabelValue.appendSplit]
    · let step : LabelDen K ⊕ LabelDen R → LabelDen K ⊕ LabelDen (A :: R) :=
        Sum.map id Sum.inr
      have map_split : (fun y : LabelDen (R ++ K) =>
          LabelValue.appendSplit (A :: R) K (.inr y)) =
          step ∘ LabelValue.appendSplit R K := by
        funext y
        cases h : LabelValue.appendSplit R K y <;>
          simp [LabelValue.appendSplit, h, step]
      change ((k.liftLabels R ρ x >>= fun y =>
        pure (Sum.inr y : LabelDen ((A :: R) ++ K))) >>= _) = _
      have mapped := congrArg (fun z => z >>= (pure ∘ step)) (ih x)
      rw [bind_assoc] at mapped
      simp only [Function.comp_apply, pure_bind] at mapped
      rw [bind_assoc]
      simp only [Function.comp_apply, pure_bind, congrFun map_split]
      cases h : LabelValue.appendSplit R L x <;>
        simp_all [LabelValue.appendSplit, step, Function.comp_def]

private theorem liftLabels_dispatch {X : Type v} (k : Continuation (m := m) Γ L K)
    (R : LCtx τ) (ρ : Env Γ) (x : LabelDen (R ++ L))
    (ret : LabelDen K → m X) (next : LabelDen R → m X) :
    (k.liftLabels R ρ x >>= fun y => Sum.elim ret next (LabelValue.appendSplit R K y)) =
      Sum.elim (fun y => k ρ y >>= ret) next (LabelValue.appendSplit R L x) := by
  have h := congrArg (fun z => z >>= Sum.elim ret next) (liftLabels_split k R ρ x)
  rw [bind_assoc] at h
  simp only [Function.comp_apply, pure_bind] at h
  rw [h]
  cases LabelValue.appendSplit R L x <;> simp [Function.comp_def]

variable [Iterate m] [LawfulElgotMonad m]

/-- Applying an effectful continuation to the outward results of a dispatcher
commutes with the iteration of its local blocks. -/
theorem cfgDenotation_continuation_proof {n : Nat} {R : Fin n → τ}
    (k : Continuation (m := m) Γ L K)
    (entry : Env Γ → m (LabelDen (List.ofFn R ++ L)))
    (blocks : Env Γ × FiniteLabelDen R → m (LabelDen (List.ofFn R ++ L))) :
    cfgDenotation (R := R)
      ((k.liftLabels (List.ofFn R)).applyTo entry)
      (fun p => blocks p >>= k.liftLabels (List.ofFn R) p.1) =
        k.applyTo (cfgDenotation (R := R) entry blocks) := by
  funext ρ
  let X := LabelDen (List.ofFn R)
  let step : X → m (LabelDen L ⊕ X) := fun x =>
    blocks (ρ, labelDenToFinite R x) >>= fun y => pure (LabelValue.appendSplit (List.ofFn R) L y)
  let step' : X → m (LabelDen K ⊕ X) := fun x =>
    (blocks (ρ, labelDenToFinite R x) >>= k.liftLabels (List.ofFn R) ρ) >>=
      fun y => pure (LabelValue.appendSplit (List.ofFn R) K y)
  have hstep : step' = mapReturn step (k ρ) := by
    funext x
    simp only [bind_assoc, step, step', mapReturn, pure_bind]
    exact bind_congr fun y => liftLabels_split k (List.ofFn R) ρ y
  have hlaw : (fun x : X => Elgot.iter step x >>= k ρ) = Elgot.iter step' :=
    (LawfulElgotMonad.naturality step (k ρ)).trans (congrArg (Elgot.iter (m := m)) hstep.symm)
  simp only [cfgDenotation, Continuation.applyTo, binaryCoproductIso_hom_labelAppendSplit]
  rw [bind_assoc, bind_assoc]
  apply bind_congr
  intro y
  calc
    _ = k.liftLabels (List.ofFn R) ρ y >>= fun z =>
        Sum.elim pure (Elgot.iter step') (LabelValue.appendSplit (List.ofFn R) K z) := by
      apply bind_congr
      intro z
      cases LabelValue.appendSplit (List.ofFn R) K z <;> rfl
    _ = Sum.elim (k ρ) (Elgot.iter step') (LabelValue.appendSplit (List.ofFn R) L y) := by
      rw [liftLabels_dispatch]
      simp only [bind_pure]
    _ = _ := by
      cases LabelValue.appendSplit (List.ofFn R) L y with
      | inl z =>
        exact (pure_bind z (k ρ)).symm
      | inr x =>
        exact (congrFun hlaw x).symm

end Silmaril.Isotope.LambdaSSA.Semantics.Monadic
