module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Wires.Defs

/-! # Partial primitives for the same typed spine -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open OrderedTheta (pack packChoice point)
open TwoBlock.TwoExit (Carrier ExitCode Route finish enter Pure callCase)
open TwoBlock.TwoExit.ExplicitRuntime (exitPayload)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [InstructionModel Φ τ ε m]
variable {A B C D : τ}

def bodyRoute (b : TyDen B) : TyDen (Route B C D) :=
  (TypeModel.coprodEquiv (ExitCode C D) B).symm (.inr b)

def lastResult (r : TyDen D ⊕ TyDen A) : OrderedTheta.ResultTuple (Carrier A C D) :=
  packChoice (Sum.map (fun d => finish (A := A) (C := C) (.inr d)) enter r)

def exitResult (out : TyDen (ExitCode C D)) : OrderedTheta.ResultTuple (Carrier A C D) :=
  packChoice (.inl ((TypeModel.coprodEquiv (ExitCode C D) A).symm (.inl out)))

def orderedModel : OrderedRuntime.Structured.Model (Pure τ) (Effect Φ) m where
  value := TyDen
  runPure := (TwoBlock.TwoExit.orderedModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)).runPure
  effect
    | .header op, data => (TwoBlock.TwoExit.orderedModel (ε := ε) (m := m)).effect (.header op) data
    | @Effect.forward _ _ _ _ B X C D op, .cons route .nil =>
      match TypeModel.coprodEquiv (ExitCode C D) B route with
      | .inl out => pure (pack ((TypeModel.coprodEquiv (ExitCode C D) X).symm (.inl out)))
      | .inr b => TwoBlock.call (ε := ε) op b >>= fun x => pure (pack (bodyRoute x))
    | @Effect.last _ _ _ _ A B C D op, .cons route .nil =>
      match TypeModel.coprodEquiv (ExitCode C D) B route with
      | .inl out => pure (exitResult out)
      | .inr b => callCase (ε := ε) op b >>= fun r => pure (lastResult r)

variable {σ : Type u} [InstructionModel Φ τ ε (StateT σ Part.{u})]

abbrev wireModel :=
  NestedTheta.ExplicitRuntime.Partial.wireModel
    (orderedModel (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))

def returns (g : Loop Φ A C D) (a : TyDen A) (initial : σ) (label : LabelDen [C, D]) (final : σ) : Prop :=
  NestedTheta.Partial.returns (wireModel (ε := ε)) g (point (enter a) initial)
    (point (finish (exitPayload label)) final)

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain
