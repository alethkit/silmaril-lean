module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Observation
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Substitution

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (Ops RegionAt PureValue Realizes ShapedObs)

universe u v w x

variable {Φ : Type u} {α : Type w} {σ : Type x} {O : Ops Φ α σ} {env : Env α}

private theorem let₂_pure {a b : Tm Φ} {l r : Value α} (ha : PureValue O env a l) (hb : PureValue O env b r)
    (p : Region Φ) : RegionAt O env (.let₂ (.pair a b) p) (extend (extend env l) r) p where
  eval := by
    intro s j a t
    constructor
    · intro run
      cases run with
      | let₂ arg body =>
        obtain ⟨eq, rfl⟩ := (ha.pair hb).unique arg
        cases eq
        exact body
    · exact fun run => .let₂ ((ha.pair hb).eval _) run
  fault := by
    intro s t
    constructor
    · intro run
      cases run with
      | let₂_arg arg => exact ((ha.pair hb).noFault arg).elim
      | let₂_body arg body =>
        obtain ⟨eq, rfl⟩ := (ha.pair hb).unique arg
        cases eq
        exact body
    · exact fun run => .let₂_body ((ha.pair hb).eval _) run
  div := by
    intro s
    constructor
    · intro run
      cases run.unfold with
      | let₂_arg arg => exact ((ha.pair hb).noDiv arg).elim
      | core step => cases step with
        | let₂ arg body =>
          obtain ⟨eq, rfl⟩ := (ha.pair hb).unique arg
          cases eq
          exact body
    · exact fun run => .fold_core (.let₂ ((ha.pair hb).eval _) run)

private theorem realize_pair {a b : Tm Φ} {l r : Value α}
    (left : PureValue O env a l) (right : PureValue O env b r) :
    Realizes O env (Tm.consSubst b (Tm.singleSubst a)) (extend (extend env l) r) := by
  intro i
  cases i with
  | zero => exact right
  | succ i => exact Realizes.single left i

theorem productBeta {κ : Type v} [HasTy Φ (Ty κ)] {Γ L : List (Ty κ)} {r t : Region Φ}
    (h : Region.ProductBeta.Step Γ r t L) : ShapedObs (α := α) (σ := σ) Γ r t := by
  intro O _ _ env _
  cases h with
  | let₂Beta ha hb _ =>
    obtain ⟨_, left⟩ := PureValue.ofBranchValue (O := O) (env := env) ha
    obtain ⟨_, right⟩ := PureValue.ofBranchValue (O := O) (env := env) hb
    exact (let₂_pure left right _).trans (((realize_pair left right).region _).symm)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent
