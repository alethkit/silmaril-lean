module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Wires.Model.Defs

/-! # Shared partial primitives and ordered acyclic activations -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open OrderedTheta (pack point results carried)
open TwoBlock.TwoExit (Carrier ExitCode Pure callCase enter finish)
open TwoBlock.TwoExit.ExplicitRuntime (exitPayload)
open OrderedRuntime.Structured (Values RuntimeValues Threaded)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [InstructionModel Φ τ ε m]
variable {A B K E D S : τ}

/-- The same typed instructions, with ordinary ordered sequencing and only
the selected arm evaluated. -/
def bodyAction : {A B : τ} → Body Φ A B → TyDen A → m (TyDen B)
  | _, _, .instruction op, a => TwoBlock.call (ε := ε) op a
  | _, _, .sequence first next, a => bodyAction first a >>= bodyAction next
  | _, _, .choice op l r, a => callCase (ε := ε) op a >>= Sum.elim (bodyAction l) (bodyAction r)

def round (s : Loop Φ A B K E D) (a : TyDen A) : m (LabelDen [E,D] ⊕ TyDen A) :=
  callCase (ε := ε) s.header a >>= fun
    | .inl e => pure (.inl (.inl e))
    | .inr b => bodyAction (ε := ε) s.body b >>= fun k => callCase (ε := ε) s.join k >>= fun
      | .inl d => pure (.inl (.inr (.inl d)))
      | .inr a => pure (.inr a)

def readRoute : {S A : τ} → Input S A → TyDen S → Option (TyDen A)
  | _, _, .direct, a => some a
  | _, _, .left, v => (TypeModel.coprodEquiv _ _ v).getLeft?
  | _, _, .right, v => (TypeModel.coprodEquiv _ _ v).getRight?

def choiceData {X Y : τ} (result : TyDen X ⊕ TyDen Y) :
    Tuple (Values (TyDen (τ := τ))) (results (Silmaril.coprod X Y)) :=
  let tag : Fin 2 := match result with | .inl _ => 0 | .inr _ => 1
  .cons ⟨tag⟩ (pack ((TypeModel.coprodEquiv X Y).symm result))

variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {σ : Type u} [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- Structural exit routing is pure. A bad guarded input has no partial
observation, and generated branches always supply the matching sum. -/
def orderedModel : OrderedRuntime.Structured.Model (Pure τ) (Effect Φ) (StateT σ Part.{u}) where
  value := TyDen
  runPure := (TwoBlock.TwoExit.orderedModel (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})).runPure
  effect
    | .header op, data => (TwoBlock.TwoExit.orderedModel (ε := ε) (m := StateT σ Part.{u})).effect (.header op) data
    | .join op, .cons k .nil => callCase (ε := ε) op k >>= fun result => pure (LinearChain.lastResult result)
    | .acyclic (.call route op), .cons v .nil =>
      match readRoute route v with
      | some a => TwoBlock.call (ε := ε) op a >>= fun b => pure (pack b)
      | none => StateT.mk fun _ => Part.none
    | .acyclic (.classify route op), .cons v .nil =>
      match readRoute route v with
      | some a => callCase (ε := ε) op a >>= fun result => pure (choiceData result)
      | none => StateT.mk fun _ => Part.none

abbrev wireModel :=
  NestedTheta.ExplicitRuntime.Partial.wireModel (orderedModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ))

namespace Wiring

open OrderedRuntime.Structured (Data runtime)

abbrev WireValues := RuntimeValues (TyDen (τ := τ)) σ

variable {args outs : Ports (OrderedRuntime.Structured.Ty τ)}
variable {past : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {a : Data args} {o : Data outs}
variable {live : Origin (Threaded args) past runtime}

/-- Evaluate a checked continuation in its current numbered scope. -/
noncomputable def eval (code : Code Φ a o live) (entry : Tuple (WireValues (τ := τ) (σ := σ)) (Threaded args))
    (locals : Locals (WireValues (τ := τ) (σ := σ)) past) :
    Part (Tuple (WireValues (τ := τ) (σ := σ)) (Threaded outs)) :=
  code.2.1.denoteOpenWith (wireModel (ε := ε) (σ := σ)) entry locals

end Wiring

/-- Encode a decoded LambdaSSA exit and its final token as the actual θ result. -/
def exitTuple (p : LabelDen [E,D] × σ) :
    Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (carried (Carrier A E D))) :=
  point (finish (exitPayload p.1)) p.2

noncomputable def observe (g : Numbered Φ A E D sigs) (a : TyDen A) (initial : σ) :=
  NestedTheta.Partial.observe (wireModel (ε := ε)) g (point (enter a) initial)

def returns (g : Numbered Φ A E D sigs) (a : TyDen A) (initial : σ) (label : LabelDen [E,D]) (final : σ) : Prop :=
  NestedTheta.Partial.returns (wireModel (ε := ε)) g (point (enter a) initial)
    (exitTuple (label, final))

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime
