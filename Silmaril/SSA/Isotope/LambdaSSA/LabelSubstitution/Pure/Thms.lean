module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Pure.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.Pure
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.PureKleisli

/-!
# Label substitution with pure branch arguments

These are the literal-syntax equations of Ghalayini and Krishnaswami,
*The Denotational Semantics of SSA*, arXiv:2411.09347v2, Theorem 5.12, in the
lawful Elgot Kleisli model. The paper types branch arguments at the bottom
effect. In this model the premise is witnessed by a pure denotation of each
argument. The categorical graph requires no choice of a canonical denotation.
-/

public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Monadic

open Silmaril.Elgot Silmaril.Isotope.LetIter.ProofRelevant.Semantics

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [InstructionModel Φ τ ε m]
  {Γ : VCtx τ} {L K : LCtx τ} {region : Region Φ}

/-- An exactly typed expression using only bottom-effect instructions has
a pure denotation by the instruction model's purity law. -/
theorem pureTerm_denotes {a : Tm Φ} {A : τ}
    (typed : Tm.HasType Γ a A) (hp : a.Pure (⊥ : ε)) :
    ∃ value : Env Γ → TyDen A, Denotes (m := m) ε typed (fun ρ => pure (value ρ)) :=
  pureTerm_denotes_proof typed hp

/-- The paper's bottom-effect branch rule supplies the semantic branch premise. -/
theorem PureBranches.br_of_pure {a : Tm Φ} {A : τ} {i : Nat}
    (hl : At L i A) (ha : Tm.HasType Γ a A) (hp : a.Pure (⊥ : ε)) :
    PureBranches (m := m) ε Γ (.br i a) L := by
  obtain ⟨_, da⟩ := pureTerm_denotes (m := m) ha hp
  exact .br hl da

/-- Constructor-valued branch arguments give pure denotations in every lawful monadic model. -/
theorem valueBranches_pure (h : Region.ValueBranches Γ region L) :
    PureBranches (m := m) ε Γ region L :=
  valueBranches_pure_proof h

variable [Iterate m] [LawfulElgotMonad m]

/-- A structural denotation of literal substitution sequences the original
region with the given continuation while retaining the environment. -/
theorem PureBranches.lsubst (h : PureBranches (m := m) ε Γ region L) {σ : Nat → Region Φ}
    {k : Continuation (m := m) Γ L K} (d : k.Denotes (ε := ε) σ) :
    ∃ (hr : Region.HasType Γ region L) (hs : Region.HasType Γ (region.lsubst σ) K)
      (f : Env Γ → m (LabelDen L)),
      RegionDenotes ε hr f ∧ RegionDenotes ε hs (k.applyTo f) :=
  pure_lsubst_proof h d

end Silmaril.Isotope.LambdaSSA.Semantics.Monadic

namespace Silmaril.Isotope.LambdaSSA.Semantics.Agreement

open CategoryTheory Silmaril.Elgot Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)

local notation "catBind" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]

/-- The region equation of Theorem 5.12(a) holds in the categorical denotation graph. -/
theorem categoricalRegion_lsubst_graph
    {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ (r.lsubst σ) K)
    (pureBranches : Monadic.PureBranches (m := m) ε Γ r L)
    (k : Monadic.Continuation (m := m) Γ L K) (d : k.Denotes (ε := ε) σ) :
    let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    let J := typeJ (m := m)
    let T := Categorical.ofMonadicTypeModel (τ := τ)
    ∃ F, Categorical.RegionDenotes J T hr F ∧
      Categorical.RegionDenotes J T hs (catBind J F (continuationArrow k)) :=
  categoricalRegion_lsubst_graph_proof hr hs pureBranches k d

/-- Coherence gives the equation of Theorem 5.12(a) for the chosen arrows. -/
theorem categoricalRegion_lsubst
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ (r.lsubst σ) K)
    (pureBranches : Monadic.PureBranches (m := m) ε Γ r L)
    (k : Monadic.Continuation (m := m) Γ L K) (d : k.Denotes (ε := ε) σ) :
    categoricalRegionDenote (ε := ε) (m := m) hs =
      catBind (typeJ (m := m)) (categoricalRegionDenote (ε := ε) (m := m) hr) (continuationArrow k) :=
  categoricalRegion_lsubst_proof coherent hr hs pureBranches k d

/-- The sequential composite denotes literal substitution into the first
family. Its categorical arrow is given by `continuationArrow_comp`, yielding
Theorem 5.12(b) for these denotations. -/
theorem continuationDenotes_compLSubst
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {L K H : LCtx τ} {σ υ : Nat → Region Φ}
    {first : Monadic.Continuation (m := m) Γ L K}
    {after : Monadic.Continuation (m := m) Γ K H}
    (dFirst : first.Denotes (ε := ε) σ) (dAfter : after.Denotes (ε := ε) υ)
    (pureBranches : ∀ ⦃i A⦄, At L i A → Monadic.PureBranches (m := m) ε (A :: Γ) (σ i) K) :
    (first.comp after).Denotes (ε := ε) (Region.compLSubst σ υ) :=
  continuationDenotes_compLSubst_proof coherent dFirst dAfter pureBranches

end Silmaril.Isotope.LambdaSSA.Semantics.Agreement
