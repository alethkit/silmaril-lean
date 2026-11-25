module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Model.Defs

/-! # Shared ordered computations for the two-block loop -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Silmaril.Elgot (Iterate)
open OrderedTheta (pack unpack exit carried results ValueTuple ResultTuple)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [InstructionModel Φ τ ε m]
/-- Dispatch a CFG label where both blocks can produce an external result. -/
def labelStepWithExits {X Y E : Type u} (head : X → m (E ⊕ Y)) (body : Y → m (E ⊕ X)) :
    X ⊕ Y → m (E ⊕ (X ⊕ Y))
  | .inl x => head x >>= fun r => pure (Sum.map id Sum.inr r)
  | .inr y => body y >>= fun r => pure (Sum.map id Sum.inl r)

variable {A B C : τ}

/-- Apply the instruction at its declared source and target boundaries. -/
def call (op : Instruction Φ A C) (a : TyDen A) : m (TyDen C) := do
  let y ← InstructionModel.denote (ε := ε) (m := m) op.op (op.input.symm ▸ a)
  pure (op.output ▸ y)

def headerAction (op : Instruction Φ A (Silmaril.coprod A B)) (a : TyDen A) :
    m (TyDen A ⊕ TyDen B) := do
  let result ← call (ε := ε) op a
  pure (TypeModel.coprodEquiv A B result)

/-- One RVSDG θ activation can call the body on a separately typed payload. -/
def round (s : Blocks Φ A B) (a : TyDen A) : m (TyDen A ⊕ TyDen A) :=
  headerAction (ε := ε) s.header a >>= fun result =>
    match result with
    | .inl a => pure (.inl a)
    | .inr b => call (ε := ε) s.body b >>= fun next => pure (.inr next)

/-- Retain the typed sum. Its constructor determines the selector. -/
def headerResult (result : TyDen A ⊕ TyDen B) :
    Tuple (OrderedRuntime.Structured.Values (TyDen (τ := τ))) (headerPorts A B) :=
  let tag : Fin 2 := match result with | .inl _ => 0 | .inr _ => 1
  .cons ⟨tag⟩ (.cons ((TypeModel.coprodEquiv A B).symm result) .nil)

def loopResult (tag : Fin 2) (a : TyDen A) : ResultTuple A := .cons ⟨tag⟩ (pack a)

/-- The saved header input makes both arm maps total at their common value
interface. The checked wiring feeds each arm the matching sum constructor. -/
def orderedModel : OrderedRuntime.Structured.Model (Pure τ) (Effect Φ) m where
  value := TyDen
  runPure
    | @Pure.exit _ _ A B, .cons saved (.cons sum .nil) =>
      loopResult 0 (Sum.elim id (fun _ => saved) (TypeModel.coprodEquiv A B sum))
  effect
    | .header op, .cons x .nil => headerAction (ε := ε) op x >>= fun result => pure (headerResult result)
    | @Effect.body _ _ _ _ A B op, .cons saved (.cons sum .nil) =>
      match TypeModel.coprodEquiv A B sum with
      | .inl _ => pure (loopResult 1 saved)
      | .inr b => call (ε := ε) op b >>= fun a => pure (loopResult 1 a)

def model : NestedTheta.MonadicModel.{u,u,u} (Op (τ := τ) Φ) m where
  value := TyDen
  snapshot _ := PUnit
  primitive := (orderedModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)).step

/-- Adapt the numbered RVSDG result to the typed LambdaSSA exit label. -/
noncomputable def denote [LawfulMonad m] [Iterate m] (g : Loop Φ A) (env : Env [A]) :
    m (LabelDen [A]) :=
  (show m (ValueTuple A) from
    (g.toTerm.denoteWith (model (ε := ε) (m := m))).of (pack env.2)) >>=
      fun output => pure (exit (unpack output))

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock
