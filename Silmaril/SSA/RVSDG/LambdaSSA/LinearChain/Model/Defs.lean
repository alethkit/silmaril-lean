module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Thms

/-! # The ordered fold of a typed LambdaSSA body -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain

open Silmaril.Elgot (Iterate iter)
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LetIter.ProofRelevant.Semantics
open TwoBlock.TwoExit (callCase exitLabel)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [InstructionModel Φ τ ε m]
variable {A B C D : τ} {tail : List τ}

/-- Sequence the body in typed dependency order. The terminal sum is
exposed only once the last instruction has completed. -/
def Body.fold : {B : τ} → {tail : List τ} → Body Φ A D B tail → TyDen B → m (TyDen D ⊕ TyDen A)
  | _, _, .last op, b => callCase (ε := ε) op b
  | _, _, .next op rest, b => TwoBlock.call (ε := ε) op b >>= rest.fold

/-- A round ends at a typed external exit or at the next header entry. -/
def round (s : Blocks Φ A B C D tail) (a : TyDen A) : m (LabelDen [C, D] ⊕ TyDen A) :=
  callCase (ε := ε) s.header a >>= fun
    | .inl c => pure (.inl (.inl c))
    | .inr b => s.body.fold (ε := ε) b >>= fun
      | .inl d => pure (.inl (.inr (.inl d)))
      | .inr a => pure (.inr a)

/-- One Elgot feedback over just the header parameters, returning a real label. -/
noncomputable def regionAction [Iterate m] (s : Blocks Φ A B C D tail) (env : Env [A]) :
    m (LabelDen [C, D]) :=
  iter (round (ε := ε) s) env.2

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain
