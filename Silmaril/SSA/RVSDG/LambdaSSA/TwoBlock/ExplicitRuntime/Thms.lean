module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Execution

/-! # Explicit wires at the typed two-block exit -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime

open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LetIter.ProofRelevant.Semantics
open OrderedTheta (exit point)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateM σ)]
variable {A B : τ} {r : Region Φ} {g : Loop Φ A}

set_option backward.isDefEq.respectTransparency false

/-- The padded erasure of the numbered explicit graph preserves and reflects
finite returns, including the unique typed exit and the final live token. -/
theorem erased_iff (s : Blocks Φ A B) (a b : TyDen A) (initial final : σ) :
    erasedObservation (ε := ε) s a initial = Part.some (exit b, final) ↔
      (graph s).Returns (wireModel (ε := ε)).toRVSDG (point a initial) (point b final) :=
  Proofs.erased_iff s a b initial final

variable [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- Lifting an instruction commutes with its checked source and target casts. -/
theorem PrimitiveAgreement.call_run (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    {X Y : τ} (op : TwoBlock.Instruction Φ X Y) (a : TyDen X) (state : σ) :
    (call (ε := ε) (m := StateT σ Part.{u}) op a).run state =
      Part.some ((call (ε := ε) (m := StateM σ) op a).run state) :=
  Proofs.call_run agrees op a state

/-- After removing the unit slot at the boundary, erasure recovers the
ordered target's denotation for every admitted translation witness. -/
theorem erased_denote (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (rel : Related A B r g) (env : Env [A]) (state : σ) :
    erasedObservation (ε := ε) rel.instructions env.2 state =
      (TwoBlock.denote (ε := ε) (m := StateT σ Part.{u}) g env).run state :=
  Proofs.erased_denote agrees rel env state

/-- The chosen LambdaSSA denotation and the numbered explicit graph have
the same finite observations at the original typed exit. -/
theorem region_returns_iff (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (coherent : Isotope.LambdaSSA.Semantics.Agreement.RegionCoherent
      (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (rel : Related A B r g) (env : Env [A]) (b : TyDen A) (initial final : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) rel.typing env).run initial =
      Part.some (exit b, final) ↔
      (graph rel.instructions).Returns (wireModel (ε := ε)).toRVSDG
        (point env.2 initial) (point b final) := by
  rw [rel.chosenDenote_eq coherent, ← erased_denote agrees rel, erased_iff]

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime
