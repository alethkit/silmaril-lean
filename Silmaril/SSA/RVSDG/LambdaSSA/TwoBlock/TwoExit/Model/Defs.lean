module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Model.Defs

/-! # Ordered semantics for the typed exit encoding -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Silmaril.Elgot (Iterate iter)
open OrderedTheta (pack unpack packChoice)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [InstructionModel Φ τ ε m]
variable {A B C D X Y : τ}

/-- Read the branch tag of a typed primitive result using the type model. -/
def callCase (op : TwoBlock.Instruction Φ X (Silmaril.coprod C Y)) (x : TyDen X) :
    m (TyDen C ⊕ TyDen Y) :=
  TwoBlock.call (ε := ε) op x >>= fun y => pure (TypeModel.coprodEquiv C Y y)

/-- One header activation and, when selected, one body activation. -/
def round (s : Blocks Φ A B C D) (a : TyDen A) : m ((TyDen C ⊕ TyDen D) ⊕ TyDen A) :=
  callCase (ε := ε) s.header a >>= fun
    | .inl c => pure (.inl (.inl c))
    | .inr b => callCase (ε := ε) s.body b >>= fun
      | .inl d => pure (.inl (.inr d))
      | .inr a => pure (.inr a)

/-- Recover separate external labels, including when their payload types coincide. -/
def exitLabel : TyDen C ⊕ TyDen D → LabelDen [C, D]
  | .inl c => .inl c
  | .inr d => .inr (.inl d)

def enter (a : TyDen A) : TyDen (Carrier A C D) :=
  (TypeModel.coprodEquiv (ExitCode C D) A).symm (.inr a)

def finish (out : TyDen C ⊕ TyDen D) : TyDen (Carrier A C D) :=
  (TypeModel.coprodEquiv (ExitCode C D) A).symm (.inl ((TypeModel.coprodEquiv C D).symm out))

/-- The decoder is defined on the full carrier. The denotation theorem
places every return in the completed summand, where decoding is pure. -/
def decode [Iterate m] (value : TyDen (Carrier A C D)) : m (LabelDen [C, D]) :=
  match TypeModel.coprodEquiv (ExitCode C D) A value with
  | .inl out => pure (exitLabel (TypeModel.coprodEquiv C D out))
  | .inr a => iter (fun header : TyDen A => pure (.inr header)) a

def routeResult (result : TyDen (ExitCode C D) ⊕ TyDen B) :
    Tuple (OrderedRuntime.Structured.Values (TyDen (τ := τ))) (headerPorts B C D) :=
  let tag : Fin 2 := match result with | .inl _ => 0 | .inr _ => 1
  .cons ⟨tag⟩ (.cons ((TypeModel.coprodEquiv (ExitCode C D) B).symm result) .nil)

def orderedModel : OrderedRuntime.Structured.Model (Pure τ) (Effect Φ) m where
  value := TyDen
  runPure
    | @Pure.exit _ _ A B C D, .cons saved (.cons route .nil) =>
      match TypeModel.coprodEquiv (ExitCode C D) B route with
      | .inl out => packChoice (.inl ((TypeModel.coprodEquiv (ExitCode C D) A).symm (.inl out)))
      | .inr _ => packChoice (.inr saved)
  effect
    | @Effect.header _ _ _ _ A B C D op, .cons x .nil =>
      match TypeModel.coprodEquiv (ExitCode C D) A x with
      | .inl out => pure (routeResult (.inl out))
      | .inr a => callCase (ε := ε) op a >>= fun result =>
        pure (routeResult (Sum.map (fun c => (TypeModel.coprodEquiv C D).symm (.inl c)) id result))
    | @Effect.body _ _ _ _ A B C D op, .cons _ (.cons route .nil) =>
      match TypeModel.coprodEquiv (ExitCode C D) B route with
      | .inl out => pure (packChoice (.inl ((TypeModel.coprodEquiv (ExitCode C D) A).symm (.inl out))))
      | .inr b => callCase (ε := ε) op b >>= fun result => pure (packChoice (Sum.map
        (fun d => finish (A := A) (C := C) (.inr d)) (enter (C := C) (D := D)) result))

def model : NestedTheta.MonadicModel.{u,u,u} (Op (τ := τ) Φ) m where
  value := TyDen
  snapshot _ := PUnit
  primitive := (orderedModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)).step

/-- Start the numbered θ at the active header and retain the typed carrier. -/
noncomputable def denoteCarrier [LawfulMonad m] [Iterate m] (g : Loop Φ A C D) (a : TyDen A) :
    m (TyDen (Carrier A C D)) :=
  (g.toTerm.denoteWith (model (ε := ε) (m := m))).of (pack (enter (C := C) (D := D) a)) >>=
    fun output => pure (unpack output)

/-- Return the real LambdaSSA exit label and its payload. -/
noncomputable def denote [LawfulMonad m] [Iterate m] (g : Loop Φ A C D) (env : Env [A]) :
    m (LabelDen [C, D]) :=
  denoteCarrier (ε := ε) (m := m) g env.2 >>= decode

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit
