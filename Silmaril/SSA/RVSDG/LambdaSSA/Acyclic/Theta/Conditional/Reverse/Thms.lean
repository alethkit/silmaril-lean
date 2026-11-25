module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse

/-! # Checked reverse fibres preserve the actual SSA observation -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A L B K E D : τ}

noncomputable def canonical (s : Guarded Φ A L B K E D) : Decomposition (graph s) B K :=
  Proofs.canonical s

theorem canonical_decode (s : Guarded Φ A L B K E D) : (canonical s).view.decode = s :=
  Proofs.canonical_decode s

theorem raise_canonical (s : Guarded Φ A L B K E D) : (raise (canonical s)).1 = region s :=
  Proofs.raise_canonical s

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {g : Graph Φ A L E D}

theorem raise_returns_iff (w : Decomposition g B K)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (label : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial label final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) (raise w).2.typing env).run initial =
        Part.some (label, final) :=
  (raise w).2.region_returns_iff coherent env label initial final

theorem raise_undefined_iff (w : Decomposition g B K)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) (raise w).2.typing env).run initial = Part.none :=
  (raise w).2.region_undefined_iff coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse
