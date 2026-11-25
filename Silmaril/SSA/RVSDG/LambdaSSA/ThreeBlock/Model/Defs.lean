module

public import Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Thms

/-! # The shared ordered computations of a three-block loop -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open OrderedTheta (carried results pack packChoice point)
open TwoBlock.TwoExit (callCase Carrier ExitCode Route finish enter exitLabel Pure)
open Silmaril.Elgot (Iterate iter)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [InstructionModel Φ τ ε m]
variable {A B X C D : τ}

/-- Run both body blocks in dependency order when the header selects them. -/
def round (s : Blocks Φ A B X C D) (a : TyDen A) :
    m ((TyDen C ⊕ TyDen D) ⊕ TyDen A) :=
  callCase (ε := ε) s.header a >>= fun
    | .inl c => pure (.inl (.inl c))
    | .inr b => TwoBlock.call (ε := ε) s.first b >>= fun x =>
      callCase (ε := ε) s.last x >>= fun r => pure (Sum.map Sum.inr id r)

/-- Enrich a body input with the completed branch, common to the arm's types. -/
def bodyRoute (x : TyDen X) : TyDen (Route X C D) :=
  (TypeModel.coprodEquiv (ExitCode C D) X).symm (.inr x)

def lastResult (r : TyDen D ⊕ TyDen A) : OrderedTheta.ResultTuple (Carrier A C D) :=
  packChoice (Sum.map (fun d => finish (A := A) (C := C) (.inr d)) enter r)

def exitResult (out : TyDen (ExitCode C D)) : OrderedTheta.ResultTuple (Carrier A C D) :=
  packChoice (.inl ((TypeModel.coprodEquiv (ExitCode C D) A).symm (.inl out)))

def orderedModel : OrderedRuntime.Structured.Model (Pure τ) (Effect Φ) m where
  value := TyDen
  runPure := (TwoBlock.TwoExit.orderedModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)).runPure
  effect
    | .header op, data => (TwoBlock.TwoExit.orderedModel (ε := ε) (m := m)).effect (.header op) data
    | @Effect.first _ _ _ _ A B X C D op, .cons _ (.cons route .nil) =>
      match TypeModel.coprodEquiv (ExitCode C D) B route with
      | .inl out => pure (pack ((TypeModel.coprodEquiv (ExitCode C D) X).symm (.inl out)))
      | .inr b => TwoBlock.call (ε := ε) op b >>= fun x => pure (pack (bodyRoute x))
    | @Effect.last _ _ _ _ A X C D op, .cons route .nil =>
      match TypeModel.coprodEquiv (ExitCode C D) X route with
      | .inl out => pure (exitResult out)
      | .inr x => callCase (ε := ε) op x >>= fun r => pure (lastResult r)

/-- Group the loop at the header and return the original LambdaSSA exit label. -/
noncomputable def regionAction [Iterate m] (s : Blocks Φ A B X C D) (env : Env [A]) :
    m (LabelDen [C, D]) :=
  iter (round (m := m) (ε := ε) s) env.2 >>= fun out => pure (exitLabel out)

variable {σ : Type u} [InstructionModel Φ τ ε (StateT σ Part.{u})]

abbrev wireModel :=
  NestedTheta.ExplicitRuntime.Partial.wireModel
    (orderedModel (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))

/-- Finite execution of a returned label's own payload and the final token. -/
def returns (g : Loop Φ A C D) (a : TyDen A) (initial : σ) (label : LabelDen [C, D]) (final : σ) : Prop :=
  NestedTheta.Partial.returns (wireModel (ε := ε)) g (point (enter a) initial)
    (point (finish (TwoBlock.TwoExit.ExplicitRuntime.exitPayload label)) final)

end Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock
