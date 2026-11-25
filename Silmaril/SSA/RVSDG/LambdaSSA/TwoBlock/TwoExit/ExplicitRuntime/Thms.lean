module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Execution

/-! # Erasure and finite returns at each typed exit -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime

open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LetIter.ProofRelevant.Semantics
open TwoBlock.ExplicitRuntime (PrimitiveAgreement)
open OrderedTheta (point)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateM σ)] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B C D : τ} {r : Isotope.LambdaSSA.Region Φ} {g : Loop Φ A C D}

set_option backward.isDefEq.respectTransparency false

/-- At the unpadded boundary erasure recovers the ordered carrier and final state. -/
theorem erasedCarrier_eq (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (rel : Related A B C D r g) (a : TyDen A) (state : σ) :
    erasedCarrier (ε := ε) rel.instructions a state =
      (denoteCarrier (ε := ε) (m := StateT σ Part.{u}) g a).run state :=
  Proofs.erasedCarrier_eq agrees rel a state

/-- Decoding the two exits preserves equality with the ordered graph denotation. -/
theorem erased_denote (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (rel : Related A B C D r g) (env : Env [A]) (state : σ) :
    erasedObservation (ε := ε) rel.instructions env.2 state =
      (denote (ε := ε) (m := StateT σ Part.{u}) g env).run state :=
  Proofs.erased_denote agrees rel env state

/-- A result of either type is observed by erasure exactly when the numbered
graph returns its completed encoding with the same live token. -/
theorem erased_returns_iff (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (s : Blocks Φ A B C D) (a : TyDen A) (out : TyDen C ⊕ TyDen D) (initial final : σ) :
    erasedObservation (ε := ε) s a initial = Part.some (exitLabel out, final) ↔
      (graph s).Returns (wireModel (ε := ε)).toRVSDG (point (enter a) initial) (point (finish out) final) :=
  Proofs.erased_returns_iff agrees s a out initial final

/-- Every coherent LambdaSSA return at either external label is preserved
and reflected by finite explicit execution, with the payload at that
label's own type and the same final token. -/
theorem region_returns_iff (agrees : PrimitiveAgreement (τ := τ) (ε := ε) (σ := σ) Φ)
    (coherent : Isotope.LambdaSSA.Semantics.Agreement.RegionCoherent
      (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (rel : Related A B C D r g) (env : Env [A]) (label : LabelDen [C, D]) (initial final : σ) :
    (Region.denote (ε := ε) (m := StateT σ Part.{u}) rel.typing env).run initial = Part.some (label, final) ↔
      (graph rel.instructions).Returns (wireModel (ε := ε)).toRVSDG (point (enter env.2) initial)
        (point (finish (exitPayload label)) final) :=
  Proofs.region_returns_iff agrees coherent rel env label initial final

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime
