module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.InstructionFree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Feedback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Defs

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Feedback.Thms

/-! # Ordinary singleton step and state-change representatives -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open ContinuationContext (single)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "F" => toInterface (τ := τ) Φ
local notation "N" => Paper.fromNative (Φ := Φ) (Γ := ([] : VCtx τ))

/-- Turn the local label into the right summand and the outward label into the left. -/
noncomputable def packStepExits (A B : τ) :
    (N).obj ((single A).append (single B)) ⟶ (F).obj (ofType B ⨿ ofType A) :=
  (appendIsColimit (Φ := Φ) (Γ := []) (single A) (single B)).desc
    (BinaryCofan.mk ((F).map (coprod.inr : ofType A ⟶ ofType B ⨿ ofType A))
      ((F).map (coprod.inl : ofType B ⟶ ofType B ⨿ ofType A)))

variable {A B D : τ} {t : Tm Φ} {p q : Region Φ}

/-- The ordinary singleton arrow represented by an exactly typed two-exit step. -/
noncomputable def stepArrow (hp : ValueBranches [A] p [A, B]) :
    ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A :=
  InducedCategory.homMk (Paper.singletonArrow hp ≫ packStepExits A B)

/-- The literal one-block feedback representative of a guarded two-exit step. -/
theorem stepFeedback_typed (hp : ValueBranches [A] p [A, B]) :
    ValueBranches [A] (feedbackRegion [A] (fun _ => p) 0) [B] :=
  (show LSubst.ValueFamily ([] : VCtx τ) [A] ([A] ++ [B]) (fun _ => p) from
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hp).feedbackRegion
      (ℓ := 0) (A := A) rfl

/-- Run a guarded singleton state change at feedback label zero, forwarding
each outward exit with its original index. -/
def regionLocalMap (r : Region Φ) : Nat → Region Φ
  | 0 => r
  | i + 1 => labelId (i + 1)

/-- Bind the state expression once before taking the singleton exit. -/
def boundReturn (ht : Tm.HasType [A] t D) : ofType (Φ := Φ) A ⟶ ofType D :=
  ofRegion (Paper.RetainedLet.returnOnce_typed ht)

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation
