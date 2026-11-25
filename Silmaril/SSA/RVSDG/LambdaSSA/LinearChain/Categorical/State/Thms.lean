module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.State.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Wires.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.State

/-! # Finite observations in the implicit and explicit state readings -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LambdaSSA.Semantics

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B E D : τ} {tail : List τ}
variable {r : Isotope.LambdaSSA.Region Φ} {g : Loop Φ A E D}

/-- The Kleisli interpretation gives the same partial state computation as the
direct region denotation, with the categorical encoding of its returned label. -/
theorem denoteState_eq (rel : Related A B E D tail r g)
    (coherent : Agreement.RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Monadic.Env [A]) :
    denoteState (ε := ε) rel.instructions env =
      Monadic.Region.denote (ε := ε) (m := StateT σ Part.{u}) rel.typing env >>= fun label =>
        pure (Monadic.LabelValue.categoricalEquiv [E,D] label) :=
  Proofs.denoteState_eq rel coherent env

/-- Successful observations of the implicit Kleisli arrow agree in both
directions with finite execution of the numbered single-token graph. -/
theorem state_returns_iff (rel : Related A B E D tail r g)
    (coherent : Agreement.RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Monadic.Env [A]) (label : Monadic.LabelDen [E,D]) (initial final : σ) :
    (denoteState (ε := ε) rel.instructions env).run initial =
      Part.some (Monadic.LabelValue.categoricalEquiv [E,D] label, final) ↔
      returns (ε := ε) g env.2 initial label final :=
  Proofs.state_returns rel coherent env label initial final

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical
