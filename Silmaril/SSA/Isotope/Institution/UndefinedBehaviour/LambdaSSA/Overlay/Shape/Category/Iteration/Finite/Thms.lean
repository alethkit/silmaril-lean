module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Semantics
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Refinement

/-! # Exact classification and refinement of certified finite overlay loops -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration

open Silmaril.Isotope (Value)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {X A B : Ty κ}
variable {M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ))}
variable {captures points results states : Nat}
variable (C : Carrier M X A B captures points results states)

/-- A deterministic internal jump contributes exactly the destination's
complete feedback observation at its carried payload and final state. -/
theorem close_branch {R : List (Ty κ)} {α : Type w} {σ : Type x} {f : Feedback.Run R [B] α σ}
    {p : Feedback.Point R.length α σ} {i : Fin R.length} {a : Value α} {s : σ}
    (run : f p = WithTop.some {Outcome.ret (Feedback.internal R [B] i) a s}) :
    Feedback.close f p = Feedback.close f (.block i a s) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.close_branch run

/-- A finite table that decodes into positional CFG block points gives
the complete observation of actual overlay closure at each coded point. -/
theorem classify_positional {R : List (Ty κ)} {f : Feedback.Run R [B] M.raw.α M.raw.σ}
    (invocation : Fin points → Fin R.length × Value M.raw.α × M.raw.σ)
    (rows : Fin points → Row points results states) (p : Fin points)
    (agrees : ∀ q, f (invocationPoint invocation q) = (rows q).positional C invocation) :
    Feedback.close f (invocationPoint invocation p) = (execute rows p).behaviour C :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.classify_positional C
    invocation rows p agrees

/-- The exact-sum classifier also accepts typed observation arrows, such as
a dispatcher selecting among multiple typed syntactic blocks. -/
theorem classify_sum
    (step : Arrow (single A) (single (.coprod B A) : Interface M.raw.α M.raw.σ M.atomType))
    (rows : Fin points → Row points results states)
    (certificate : ∀ q, step.run 0 (C.invocation q).1 (C.invocation q).2 = (rows q).behaviour C)
    (p : Fin points) :
    (iterateSum step).run 0 (C.invocation p).1 (C.invocation p).2 =
      (execute rows p).behaviour C :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.classify_sum C step rows certificate p

/-- The checker compares precisely the decoded observations at every code. -/
theorem check_behaviour_iff (lower upper : Table captures points results states) :
    check lower upper = true ↔ ∀ c p,
      (execute (lower c) p).behaviour C ≤ (execute (upper c) p).behaviour C := by
  simp [check, List.all_eq_true, Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.behaviour_order]

/-- The executable classification gives the whole shaped observation.
A scan that finds no terminal row denotes ordinary divergence. -/
theorem classify (r : Region Φ [A, X] [.coprod B A]) (table : Table captures points results states)
    (certificate : Certified C r table) (c : Fin captures) (p : Fin points) :
    (iterateCaptured M r).run 0 (pairPayload (C.capture c) (C.invocation p).1) (C.invocation p).2 =
      (execute (table c) p).behaviour C :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.classify C r table certificate c p

/-- At every coded start the check decides the existing pointwise shaped
refinement order, with more permissive behaviours on the right. -/
theorem check_iff (lower upper : Table captures points results states)
    {r t : Region Φ [A, X] [.coprod B A]}
    (hr : Certified C r lower) (ht : Certified C t upper) :
    check lower upper = true ↔ ∀ c p,
      (iterateCaptured M r).run 0 (pairPayload (C.capture c) (C.invocation p).1) (C.invocation p).2 ≤
      (iterateCaptured M t).run 0 (pairPayload (C.capture c) (C.invocation p).1) (C.invocation p).2 :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.check_iff C lower upper hr ht

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
