module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Denotation.Agreement.Full

public section

namespace Silmaril.Isotope.LambdaSSA.Semantics

open CategoryTheory Silmaril.Elgot
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (typeJ bind_of pair_of caseWithContext_of comp_map_of contextualLoop_of)

universe u v q r

namespace Agreement

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]


omit [Iterate m] [LawfulElgotMonad m] in
/-- The chosen categorical and direct monadic term denotations agree
pointwise.  Coherence is explicit because extrinsic instruction typing may
carry semantically relevant evidence. -/
theorem categoricalTermDenote_eq_proof
    (coherent : TermCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {t : Tm Φ} {A : τ} (h : Tm.HasType Γ t A)
    (ρ : Monadic.Env Γ) :
    (categoricalTermDenote (ε := ε) (m := m) h).of
        (envToCategorical ρ) =
      Monadic.denote (ε := ε) (m := m) h ρ := by
  let _ := Categorical.ofMonadicInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  let _ : Categorical.TypingCoherent (Φ := Φ)
      (typeJ (m := m)) (Categorical.ofMonadicTypeModel (τ := τ)) := coherent
  rcases denotes_toCategorical
      (Monadic.denote_spec (ε := ε) (m := m) h) with ⟨F, dF, hF⟩
  have hchosen := Categorical.Denotes.eq_denote (typeJ (m := m)) (Categorical.ofMonadicTypeModel (τ := τ)) dF
  rw [categoricalTermDenote, ← hchosen]
  exact congrFun hF ρ

/-- The chosen categorical and direct monadic region/CFG denotations agree
pointwise, including their complete-Elgot iteration clauses. -/
theorem categoricalRegionDenote_eq_proof
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ region L) (ρ : Monadic.Env Γ) :
    (categoricalRegionDenote (ε := ε) (m := m) h).of
        (envToCategorical ρ) =
      (Monadic.Region.denote (ε := ε) (m := m) h ρ >>= fun x =>
        pure (Monadic.LabelValue.categoricalEquiv L x)) := by
  let _ := Categorical.ofMonadicInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  let _ : Categorical.RegionTypingCoherent (Φ := Φ)
      (typeJ (m := m)) (Categorical.ofMonadicTypeModel (τ := τ)) := coherent
  rcases regionDenotes_toCategorical
      (Monadic.Region.denote_spec (ε := ε) (m := m) h) with ⟨F, dF, hF⟩
  have hchosen := Categorical.RegionDenotes.eq_denote
    (typeJ (m := m)) (Categorical.ofMonadicTypeModel (τ := τ)) dF
  rw [categoricalRegionDenote, ← hchosen]
  exact congrFun hF ρ

end Agreement
end Silmaril.Isotope.LambdaSSA.Semantics
