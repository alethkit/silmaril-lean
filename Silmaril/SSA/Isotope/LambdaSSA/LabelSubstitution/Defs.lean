module

public import Silmaril.SSA.Isotope.LambdaSSA.Renaming.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms

/-! # Continuations in the direct λSSA semantics -/

@[expose] public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Monadic

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {m : Type v → Type v} [Monad m]

/-- An effectful continuation sees the captured environment and the exit payload. -/
abbrev Continuation (Γ : VCtx τ) (L K : LCtx τ) :=
  Env Γ → LabelDen L → m (LabelDen K)

/-- A continuation under local labels preserves their destinations and acts
only on the outward alternatives. -/
def Continuation.liftLabels {Γ : VCtx τ} {L K : LCtx τ} (k : Continuation (m := m) Γ L K) :
    (R : LCtx τ) → Continuation (m := m) Γ (R ++ L) (R ++ K)
  | [], ρ, x => k ρ x
  | _ :: _, _, .inl a => pure (.inl a)
  | _ :: R, ρ, .inr x => k.liftLabels R ρ x >>= fun y => pure (.inr y)

/-- Retain the current environment when supplying an exit to a continuation. -/
def Continuation.applyTo {Γ : VCtx τ} {L K : LCtx τ} (k : Continuation (m := m) Γ L K)
    (f : Env Γ → m (LabelDen L)) : Env Γ → m (LabelDen K) :=
  fun ρ => f ρ >>= k ρ

/-- Compose two continuations while retaining the same captured values. -/
def Continuation.comp {Γ : VCtx τ} {L K H : LCtx τ}
    (first : Continuation (m := m) Γ L K) (after : Continuation (m := m) Γ K H) :
    Continuation (m := m) Γ L H :=
  fun γ x => first γ x >>= after γ

variable [Silmaril.Elgot.Iterate m] {Φ : Type q} [HasTy Φ τ]
  {ε : Type r} [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε m]

/-- The continuation arrow agrees with each typed replacement at its label
injection. Each replacement may have effects or a nested CFG. -/
def Continuation.Denotes {Γ : VCtx τ} {L K : LCtx τ}
    (k : Continuation (m := m) Γ L K) (σ : Nat → Region Φ) : Prop :=
  ∀ ⦃i A⦄ (h : At L i A), ∃ d : Region.HasType (A :: Γ) (σ i) K,
    RegionDenotes ε d (fun γ => k γ.1 (LabelValue.inject i h γ.2))

end Silmaril.Isotope.LambdaSSA.Semantics.Monadic

namespace Silmaril.Isotope.LambdaSSA.Semantics.Agreement

open CategoryTheory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {m : Type v → Type v} [Monad m] [LawfulMonad m]

/-- The Kleisli continuation arrow on the selected categorical environment
product and label coproducts. -/
noncomputable def continuationArrow {Γ : VCtx τ} {L K : LCtx τ}
    (k : Monadic.Continuation (m := m) Γ L K) :
    (typeJ (m := m)).obj
      (Categorical.ctxObj (Categorical.ofMonadicTypeModel (τ := τ)) Γ ×
        Monadic.CategoricalLabelDen L) ⟶
      (typeJ (m := m)).obj (Monadic.CategoricalLabelDen K) :=
  .mk (↾fun p => show m (Monadic.CategoricalLabelDen K) from
    k (envFromCategorical p.1) ((Monadic.LabelValue.categoricalEquiv L).symm p.2) >>=
      fun x => pure (Monadic.LabelValue.categoricalEquiv K x))

end Silmaril.Isotope.LambdaSSA.Semantics.Agreement

namespace Silmaril.Isotope.LambdaSSA.Region

/-- Compose two families by binding each intermediate branch argument once.
The original label argument remains bound while the first continuation runs. -/
def boundCompLSubst {Φ : Type q} (first after : Nat → Region Φ) (i : Nat) : Region Φ :=
  (first i).bindBranchArguments.lsubst (liftLSubstVars after)

end Silmaril.Isotope.LambdaSSA.Region
