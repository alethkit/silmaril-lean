module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgRealization

/-! # Rewrite the explicit carried realization of a one-block CFG -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg

open CategoryTheory
open Paper.TypeCategory (ofRegion sumIso)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X S D : τ}

/-- Tag a repeat or exit while reading the capture from the same value slot. -/
theorem tagCarriedExit_valueFamily (K Z : τ) :
    LSubst.ValueFamily (Φ := Φ) [K, X, Z] [S, D]
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)] tagCarriedExit :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgRealization.tagCarriedExit_valueFamily K Z

/-- Tag the two exits of a decoded, guarded block while retaining its capture. -/
theorem realizeStep_typed {p : Region Φ} (hp : ValueBranches [S, X] p [S, D]) :
    ValueBranches [Silmaril.product X S] (realizeStep p)
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgRealization.realizeStep_typed hp

/-- The actual packed block realizes a guarded exact-sum step. -/
theorem realizePackedStep_typed {b : Region Φ}
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]]) :
    ValueBranches [Silmaril.product X S] (realizePackedStep S D b)
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgRealization.realizePackedStep_typed hb

/-- Exact-sum iteration followed by the result projection is literal
feedback over the captured state. -/
theorem realize_loop {p : Region Φ} (hp : ValueBranches [S, X] p [S, D]) :
    Paper.Eqv [Silmaril.product X S]
      ((SyntacticCategory.iterateRegion (Silmaril.product X S) (realizeStep p)).lsubst
        (liftLSubstVars (fun _ => dropCapture)))
      (feedbackRegion [Silmaril.product X S] (fun _ => carryBlock p) 0) [D] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgRealization.realize_loop hp

/-- At the packed entry's exit, the two dispatchers select the same carried
loop on repeat and forward the original payload on exit. -/
theorem realize_exitContinuation {b : Region Φ}
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]]) :
    Paper.Eqv [packedExitType [S, D], X]
      (canonicalExitContinuation X S (realizePackedStep S D b))
      (carriedExitContinuation X S D b) [D] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgRealization.realize_exitContinuation hb

/-- The original guarded one-block CFG and the explicit carried realization
are equivalent in the existing Paper relation. -/
theorem canonicalRegion_eq_guardedCfg_realize {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]]) :
    Paper.Eqv [X] (canonicalRegion X S e (realizePackedStep S D b)) (guardedCfg S D e b) [D] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgRealization.canonicalRegion_eq_guardedCfg_realize he hb

/-- Replace the step by any guarded representative of the same arrow in the
syntactic Paper quotient after applying its exact-sum comparison. -/
theorem canonicalRegion_eq_guardedCfg_of_stepArrow {e b step : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]])
    (hs : ValueBranches [Silmaril.product X S] step
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)])
    (h : ofRegion (τ := τ) hs ≫ (sumIso (Silmaril.product X D) (Silmaril.product X S)).hom =
      ofRegion (τ := τ) (realizePackedStep_typed hb) ≫
        (sumIso (Silmaril.product X D) (Silmaril.product X S)).hom) :
    Paper.Eqv [X] (canonicalRegion X S e step) (guardedCfg S D e b) [D] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgRealization.canonicalRegion_eq_guardedCfg_of_stepArrow
    he hb hs h

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
