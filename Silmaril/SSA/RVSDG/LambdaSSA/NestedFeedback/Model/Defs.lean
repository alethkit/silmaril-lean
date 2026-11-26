module

public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Model.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Defs

/-! # Shared partial instructions for the flat CFG and its explicit graph -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open TwoBlock.TwoExit (callCase)
open OrderedTheta (carried results point pack packChoice)
open OrderedRuntime.Structured
open Silmaril.Elgot (Iterate iter)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {A B K D : τ}

section Monad

variable {m : Type u → Type u} [Monad m] [Iterate m] [InstructionModel Φ τ ε m]

def round (s : Loop Φ A B K D) (a : TyDen A) : m (TyDen D ⊕ TyDen A) :=
  TwoBlock.call (ε := ε) s.enter a >>= iter (callCase (ε := ε) s.inner) >>= callCase (ε := ε) s.finish

end Monad

def start (a : TyDen A) : TyDen (Carrier A D) :=
  (TypeModel.coprodEquiv D A).symm (.inr a)

def done (d : TyDen D) : TyDen (Carrier A D) :=
  (TypeModel.coprodEquiv D A).symm (.inl d)

def encodeStep (r : TyDen D ⊕ TyDen A) : Tuple (Values (TyDen (τ := τ))) (results (Carrier A D)) :=
  packChoice (Sum.map done start r)

variable {σ : Type u} [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- The tag and coproduct packing are pure operations on values. The graph
reaches each instruction only on its typed entry summand. -/
def orderedModel : OrderedRuntime.Structured.Model (Pure τ) (Effect Φ) (StateT σ Part.{u}) where
  value := TyDen
  runPure op _ := nomatch op
  effect
    | .enter op, .cons v .nil =>
      match TypeModel.coprodEquiv _ _ v with
      | .inr a => TwoBlock.call (ε := ε) op a >>= fun b => pure (pack (start b))
      | .inl _ => StateT.mk fun _ => Part.none
    | .inner op, .cons v .nil =>
      match TypeModel.coprodEquiv _ _ v with
      | .inr b => callCase (ε := ε) op b >>= fun r => pure (encodeStep r)
      | .inl _ => StateT.mk fun _ => Part.none
    | .finish op, .cons v .nil =>
      match TypeModel.coprodEquiv _ _ v with
      | .inl k => callCase (ε := ε) op k >>= fun r => pure (encodeStep r)
      | .inr _ => StateT.mk fun _ => Part.none

abbrev wireModel :=
  NestedTheta.ExplicitRuntime.Partial.wireModel (orderedModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ))

abbrev Point (σ : Type u) (Q : τ) := Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (carried Q))
abbrev StepResult (σ : Type u) (Q : τ) := Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (results Q))

def tagged (p : (TyDen D ⊕ TyDen A) × σ) : StepResult σ (Carrier A D) :=
  TwoBlock.ExplicitRuntime.Skeleton.tagged start done p

def entryTuple (p : TyDen A × σ) : Point σ (Carrier A D) := point (start p.1) p.2

def outputTuple (p : TyDen D × σ) : Point σ (Carrier A D) := point (done p.1) p.2

def exitTuple (p : LabelDen [D] × σ) : Point σ (Carrier A D) :=
  match p with
  | (.inl d, s) => outputTuple (d, s)
  | (.inr impossible, _) => nomatch impossible

noncomputable def observe (g : Graph Φ A D) (a : TyDen A) (initial : σ) : Part (Point σ (Carrier A D)) :=
  NestedTheta.Partial.observe (wireModel (ε := ε)) g (entryTuple (a, initial))

def returns (g : Graph Φ A D) (a : TyDen A) (initial : σ) (d : TyDen D) (final : σ) : Prop :=
  NestedTheta.Partial.returns (wireModel (ε := ε)) g (entryTuple (a, initial)) (outputTuple (d, final))

end Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback
