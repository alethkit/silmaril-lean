module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.Dispatcher
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.Soundness
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.Kleisli

/-!
# Semantic label substitution in the lawful Kleisli model

The bind-first form uses the repository's exact typing and existing branch
normalization. It implements the sequencing equation of Theorem 5.12 of
Ghalayini and Krishnaswami, *The Denotational Semantics of SSA*
(arXiv:2411.09347v2), with an explicit let at each branch. The continuation
can have effects and can itself be a CFG.
-/

public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Monadic

open Silmaril.Elgot Silmaril.Isotope.LetIter.ProofRelevant.Semantics

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  {Γ : VCtx τ} {L K : LCtx τ}

/-- Running a continuation on outward exits commutes with local CFG iteration. -/
theorem cfgDenotation_continuation {n : Nat} {R : Fin n → τ}
    (k : Continuation (m := m) Γ L K)
    (entry : Env Γ → m (LabelDen (List.ofFn R ++ L)))
    (blocks : Env Γ × FiniteLabelDen R → m (LabelDen (List.ofFn R ++ L))) :
    cfgDenotation (R := R) ((k.liftLabels (List.ofFn R)).applyTo entry)
      (fun p => blocks p >>= k.liftLabels (List.ofFn R) p.1) =
        k.applyTo (cfgDenotation (R := R) entry blocks) :=
  cfgDenotation_continuation_proof k entry blocks

variable {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
  [InstructionModel Φ τ ε m] {σ : Nat → Region Φ} {k : Continuation (m := m) Γ L K}

omit [LawfulMonad m] [LawfulElgotMonad m] in
/-- Every typed substitution has a continuation denotation. -/
theorem continuation_exists (hσ : Region.LSubst.HasType Γ L K σ) :
    ∃ k : Continuation (m := m) Γ L K, k.Denotes (ε := ε) σ :=
  continuation_exists_proof hσ

/-- Exact denotation after binding each branch argument once and substituting
arbitrary typed continuations. The conclusion uses the structural graph. -/
theorem RegionDenotes.bound_lsubst {region : Region Φ}
    {hr : Region.HasType Γ region L} {f : Env Γ → m (LabelDen L)}
    (den : RegionDenotes ε hr f) (cont : k.Denotes (ε := ε) σ) :
    ∃ ht : Region.HasType Γ (region.bindBranchArguments.lsubst σ) K,
      RegionDenotes ε ht (k.applyTo f) :=
  RegionDenotes.bound_lsubst_proof den cont

/-- Sequential continuation composition denotes the bind-first syntax for
composed substitutions. -/
theorem Continuation.Denotes.comp {H : LCtx τ} {υ : Nat → Region Φ}
    {after : Continuation (m := m) Γ K H}
    (first : k.Denotes (ε := ε) σ) (second : after.Denotes (ε := ε) υ) :
    (k.comp after).Denotes (ε := ε) (Region.boundCompLSubst σ υ) :=
  continuation_comp_proof first second

end Silmaril.Isotope.LambdaSSA.Semantics.Monadic

namespace Silmaril.Isotope.LambdaSSA.Semantics.Agreement

open CategoryTheory Silmaril.Elgot Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]

/-- The canonical categorical image of a direct denotation witnesses the
substitution equation in the categorical graph. No choice of denotation
or typing-coherence assumption is needed. -/
theorem categoricalRegion_bound_lsubst_graph
    {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    {hr : Region.HasType Γ r L} {f : Monadic.Env Γ → m (Monadic.LabelDen L)}
    (df : Monadic.RegionDenotes ε hr f)
    (k : Monadic.Continuation (m := m) Γ L K) (d : k.Denotes (ε := ε) σ) :
    let _ := Categorical.ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    let J := typeJ (m := m)
    let T := Categorical.ofMonadicTypeModel (τ := τ)
    ∃ F, Categorical.RegionDenotes J T hr F ∧
      ∃ hs : Region.HasType Γ (r.bindBranchArguments.lsubst σ) K,
        Categorical.RegionDenotes J T hs
          (Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J F (continuationArrow k)) :=
  categoricalRegion_bound_lsubst_graph_proof df k d

/-- The chosen categorical λSSA denotation satisfies the region equation of
Theorem 5.12 for bind-first substitution in a coherent lawful Kleisli model. -/
theorem categoricalRegion_bound_lsubst
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : Region.HasType Γ r L)
    (hs : Region.HasType Γ (r.bindBranchArguments.lsubst σ) K)
    (k : Monadic.Continuation (m := m) Γ L K) (d : k.Denotes (ε := ε) σ) :
    categoricalRegionDenote (ε := ε) (m := m) hs =
      Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
        (typeJ (m := m)) (categoricalRegionDenote (ε := ε) (m := m) hr) (continuationArrow k) :=
  categoricalRegion_bound_lsubst_proof coherent hr hs k d

omit [HasTy Φ τ] [HasEff Φ ε] [Bot ε] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m] in
/-- The categorical equation for composing continuations. The pure projection
retains the captured values and discards the previous label argument. -/
theorem continuationArrow_comp {Γ : VCtx τ} {L K H : LCtx τ}
    (first : Monadic.Continuation (m := m) Γ L K)
    (after : Monadic.Continuation (m := m) Γ K H) :
    let E := Categorical.ctxObj (Categorical.ofMonadicTypeModel (τ := τ)) Γ
    let J := typeJ (m := m)
    let forget : (E × Monadic.CategoricalLabelDen L) × Monadic.CategoricalLabelDen K →
        E × Monadic.CategoricalLabelDen K := fun p => (p.1.1, p.2)
    continuationArrow (first.comp after) =
      Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J
        (continuationArrow first) (J.map (↾forget) ≫ continuationArrow after) :=
  continuationArrow_comp_proof first after

end Silmaril.Isotope.LambdaSSA.Semantics.Agreement
