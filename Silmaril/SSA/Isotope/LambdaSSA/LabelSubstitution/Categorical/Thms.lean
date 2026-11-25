module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Pure.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.Categorical

/-! # Label substitution for arbitrary typed Kleisli continuation arrows -/

public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Agreement

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]

local notation "J" => typeJ (m := m)
local notation "T" => Categorical.ofMonadicTypeModel (τ := τ)
local notation "catBind" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

/-- The monadic and categorical continuation denotations agree on each label summand. -/
theorem continuationArrow_denotes {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    {k : Monadic.Continuation (m := m) Γ L K} (d : k.Denotes (ε := ε) σ) :
    let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    Categorical.ContinuationDenotes J T σ (continuationArrow k) :=
  continuationArrow_denotes_proof d

/-- Every categorical continuation denotation in a coherent lawful Elgot
Kleisli model is the image of a monadic continuation denotation. -/
theorem continuationArrow_exists
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (k : (J).obj (Categorical.ctxObj T Γ ⊗ Monadic.CategoricalLabelDen L) ⟶
      (J).obj (Monadic.CategoricalLabelDen K)) :
    let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    Categorical.ContinuationDenotes J T σ k →
      ∃ c : Monadic.Continuation (m := m) Γ L K, c.Denotes (ε := ε) σ ∧ continuationArrow c = k :=
  continuationArrow_exists_proof coherent k

/-- Literal substitution satisfies the categorical bind equation in the
denotation graph for any arrow denoting the typed continuation family. -/
theorem categoricalRegion_lsubst_of_continuationDenotes_graph
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ (r.lsubst σ) K)
    (pureBranches : Monadic.PureBranches (m := m) ε Γ r L)
    (k : (J).obj (Categorical.ctxObj T Γ ⊗ Monadic.CategoricalLabelDen L) ⟶
      (J).obj (Monadic.CategoricalLabelDen K)) :
    let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    Categorical.ContinuationDenotes J T σ k →
      ∃ F, Categorical.RegionDenotes J T hr F ∧ Categorical.RegionDenotes J T hs (catBind J F k) :=
  categoricalRegion_lsubst_of_continuationDenotes_graph_proof coherent hr hs pureBranches k

/-- Theorem 5.12(a) as equality of the chosen categorical arrows, with an
arbitrary well-typed continuation arrow in the coherent Kleisli model. -/
theorem categoricalRegion_lsubst_of_continuationDenotes
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ (r.lsubst σ) K)
    (pureBranches : Monadic.PureBranches (m := m) ε Γ r L)
    (k : (J).obj (Categorical.ctxObj T Γ ⊗ Monadic.CategoricalLabelDen L) ⟶
      (J).obj (Monadic.CategoricalLabelDen K)) :
    let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    Categorical.ContinuationDenotes J T σ k →
      categoricalRegionDenote (ε := ε) (m := m) hs =
        catBind J (categoricalRegionDenote (ε := ε) (m := m) hr) k :=
  categoricalRegion_lsubst_of_continuationDenotes_proof coherent hr hs pureBranches k

/-- Theorem 5.12(b) for arbitrary well-typed Kleisli continuation arrows.
Categorical sequencing denotes the literal composed family. -/
theorem continuationDenotes_compose
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {L K H : LCtx τ} {σ υ : Nat → Region Φ}
    (first : (J).obj (Categorical.ctxObj T Γ ⊗ Monadic.CategoricalLabelDen L) ⟶
      (J).obj (Monadic.CategoricalLabelDen K))
    (after : (J).obj (Categorical.ctxObj T Γ ⊗ Monadic.CategoricalLabelDen K) ⟶
      (J).obj (Monadic.CategoricalLabelDen H))
    (pureBranches : ∀ ⦃i A⦄, At L i A → Monadic.PureBranches (m := m) ε (A :: Γ) (σ i) K) :
    let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    Categorical.ContinuationDenotes J T σ first → Categorical.ContinuationDenotes J T υ after →
      Categorical.ContinuationDenotes J T (Region.compLSubst σ υ)
        (Categorical.composeContinuations J T (Γ := Γ) (L := L) (K := K) (H := H) first after) :=
  continuationDenotes_compose_proof coherent first after pureBranches

end Silmaril.Isotope.LambdaSSA.Semantics.Agreement
