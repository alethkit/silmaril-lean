module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Defs

/-! # Numbered explicit-wire elaboration for the admitted two-exit CFG -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime

open OrderedTheta (carriedData resultData)
open OrderedRuntime.Structured (Threaded)
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open Isotope.LetIter.ProofRelevant.Semantics

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B C D : τ}

namespace Wiring
open TwoBlock.ExplicitRuntime.Skeleton (Closed armData)

abbrev header (s : Blocks Φ A B C D) :
    Op Φ (OrderedTheta.carried (Carrier A C D)) (headerPorts B C D) :=
  .effect (.header s.header)

def arms (s : Blocks Φ A B C D) :
    Fin 2 → Closed (Pure τ) (Effect Φ) (armData (Carrier A C D) (Route B C D))
      (resultData (Carrier A C D)) [Threaded (OrderedTheta.results (Carrier A C D))] :=
  Fin.cases (TwoBlock.ExplicitRuntime.Skeleton.arm (.pure Pure.exit))
    (fun _ => TwoBlock.ExplicitRuntime.Skeleton.arm (.effect (.body s.body)))

end Wiring

abbrev WireLoop (Φ : Type u) [HasTy Φ τ] (A C D : τ) :=
  TwoBlock.ExplicitRuntime.Skeleton.WireLoop (Pure τ) (Effect Φ) (Carrier A C D)

/-- Keep the numbered two-exit γ/θ shape and append its single live token. -/
def graph (s : Blocks Φ A B C D) : WireLoop Φ A C D :=
  TwoBlock.ExplicitRuntime.Skeleton.graph (Wiring.header s) (Wiring.arms s)

def graphChecked (s : Blocks Φ A B C D) :
    NestedTheta.ExplicitRuntime.EntryChecked (a := carriedData (Carrier A C D))
      (b := carriedData (Carrier A C D)) (graph s).toTerm :=
  TwoBlock.ExplicitRuntime.Skeleton.graphChecked (Wiring.header s) (Wiring.arms s)

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable [InstructionModel Φ τ ε (StateM σ)]

abbrev wireModel := orderedModel (τ := τ) (Φ := Φ) (ε := ε) (m := StateM σ)

/-- Retain the payload at its own external label when encoding a return. -/
def exitPayload : LabelDen [C, D] → TyDen C ⊕ TyDen D
  | .inl c => .inl c
  | .inr (.inl d) => .inr d
  | .inr (.inr impossible) => nomatch impossible

/-- Interpret the erased numbered graph and keep the raw carrier and final token. -/
noncomputable def erasedCarrier (s : Blocks Φ A B C D) (a : TyDen A) (state : σ) :
    Part.{u} (TyDen (Carrier A C D) × σ) :=
  TwoBlock.ExplicitRuntime.Skeleton.observeCarrier (Wiring.header s) (Wiring.arms s)
    (wireModel (ε := ε)) (enter a) state

/-- Decode the original labels from the erased result while retaining its final token. -/
noncomputable def erasedObservation (s : Blocks Φ A B C D) (a : TyDen A) (state : σ) :
    Part.{u} (LabelDen [C, D] × σ) :=
  (erasedCarrier (ε := ε) s a state).bind (fun (carrier, token) =>
    (decode (m := StateT σ Part.{u}) carrier).run token)

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime
