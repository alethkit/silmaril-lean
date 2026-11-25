module

public import Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Wires.Model.Defs

/-! # Shared partial actions and finite observations of the numbered diamond -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open OrderedTheta (carried pack point)
open TwoBlock.TwoExit (Pure Carrier ExitCode Route callCase enter finish exitLabel)
open TwoBlock.TwoExit.ExplicitRuntime (exitPayload)
open OrderedRuntime.Structured (Values)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [InstructionModel Φ τ ε m]
variable {A B X Y K E D : τ}

/-- The classifier's payload is delivered to exactly the selected arm. -/
def runArm (s : Branches Φ B X Y K) : TyDen X ⊕ TyDen Y → m (TyDen K) :=
  Sum.elim (TwoBlock.call (ε := ε) s.left) (TwoBlock.call (ε := ε) s.right)

def bodyAction (s : Blocks Φ A B X Y K E D) (b : TyDen B) : m (TyDen D ⊕ TyDen A) :=
  callCase (ε := ε) s.diamond.classifier b >>= fun result =>
    runArm (ε := ε) s.diamond result >>= callCase (ε := ε) s.join

/-- A complete activation either exits at a typed label or restarts the header. -/
def round (s : Blocks Φ A B X Y K E D) (a : TyDen A) : m (LabelDen [E,D] ⊕ TyDen A) :=
  callCase (ε := ε) s.header a >>= fun
    | .inl e => pure (.inl (.inl e))
    | .inr b => bodyAction (ε := ε) s b >>= fun
      | .inl d => pure (.inl (.inr (.inl d)))
      | .inr a => pure (.inr a)

def branchResult (result : TyDen X ⊕ TyDen Y) : Tuple (Values (TyDen (τ := τ))) (branchOut X Y) :=
  let tag : Fin 2 := match result with | .inl _ => 0 | .inr _ => 1
  .cons ⟨tag⟩ (pack ((TypeModel.coprodEquiv X Y).symm result))

variable {σ : Type u} [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- The shared instructions are the only effects. Ill-matched branch payloads
have no successful observation. The generated γ always supplies the matching one. -/
def orderedModel : OrderedRuntime.Structured.Model (Pure τ) (Effect Φ) (StateT σ Part.{u}) where
  value := TyDen
  runPure := (TwoBlock.TwoExit.orderedModel (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})).runPure
  effect
    | .header op, data => (TwoBlock.TwoExit.orderedModel (ε := ε) (m := StateT σ Part.{u})).effect (.header op) data
    | @Effect.classifier _ _ _ _ A B X Y E D op, .cons _ (.cons route .nil) =>
      match TypeModel.coprodEquiv (ExitCode E D) B route with
      | .inl _ => StateT.mk fun _ => Part.none
      | .inr b => callCase (ε := ε) op b >>= fun xy => pure (branchResult xy)
    | @Effect.left _ _ _ _ X Y K op, .cons payload .nil =>
      match TypeModel.coprodEquiv X Y payload with
      | .inl x => TwoBlock.call (ε := ε) op x >>= fun k => pure (pack k)
      | .inr _ => StateT.mk fun _ => Part.none
    | @Effect.right _ _ _ _ X Y K op, .cons payload .nil =>
      match TypeModel.coprodEquiv X Y payload with
      | .inl _ => StateT.mk fun _ => Part.none
      | .inr y => TwoBlock.call (ε := ε) op y >>= fun k => pure (pack k)
    | .join op, .cons k .nil =>
      callCase (ε := ε) op k >>= fun result => pure (LinearChain.lastResult result)

abbrev wireModel :=
  NestedTheta.ExplicitRuntime.Partial.wireModel (orderedModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ))

/-- The finite graph observation at a decoded LambdaSSA exit. The token is
observed separately from the typed label and payload. -/
def returns (g : Loop Φ A E D) (a : TyDen A) (initial : σ) (label : LabelDen [E,D]) (final : σ) : Prop :=
  NestedTheta.Partial.returns (wireModel (ε := ε)) g (point (enter a) initial)
    (point (finish (exitPayload label)) final)

end Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime
