module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Denotation.Agreement.Full
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Kleisli

/-! # Agreement of direct and categorical LambdaSSA denotations -/

public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Agreement

open CategoryTheory Silmaril.Elgot
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [InstructionModel Φ τ ε m]

/-- Under expression typing coherence the chosen Kleisli arrow computes the
direct monadic denotation at each corresponding input. -/
theorem categoricalTermDenote_eq
    (coherent : TermCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {t : Tm Φ} {A : τ} (h : Tm.HasType Γ t A) (ρ : Monadic.Env Γ) :
    (categoricalTermDenote (ε := ε) (m := m) h).of (envToCategorical ρ) =
      Monadic.denote (ε := ε) (m := m) h ρ :=
  categoricalTermDenote_eq_proof coherent h ρ

/-- Under region typing coherence the chosen Kleisli arrow computes the
direct monadic region denotation after transporting the exit label and payload. -/
theorem categoricalRegionDenote_eq [Iterate m] [LawfulElgotMonad m]
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ r L) (ρ : Monadic.Env Γ) :
    (categoricalRegionDenote (ε := ε) (m := m) h).of (envToCategorical ρ) =
      (Monadic.Region.denote (ε := ε) (m := m) h ρ >>= fun x =>
        pure (Monadic.LabelValue.categoricalEquiv L x)) :=
  categoricalRegionDenote_eq_proof coherent h ρ

end Silmaril.Isotope.LambdaSSA.Semantics.Agreement
