module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.LocalLabels.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ContinuationLocalLabels

/-! # Continuation transport under local CFG binders -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- The lifted continuation denotes the lifted typed family. Its local
alternatives return their label and payload unchanged. -/
theorem ContinuationDenotes.liftLocalLabels {n : Nat} (R : Fin n → τ)
    {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (d : ContinuationDenotes J M σ k) :
    ContinuationDenotes J M (Region.liftLSubstN n σ) (Categorical.liftLocalLabels J M (List.ofFn R) k) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.continuation_liftLocalLabels J M R d

/-- Sequencing a continuation after the collective block arrow commutes
with restriction to any block summand. Each continuation retains only the
shared captured environment. -/
theorem CollectiveDenotes.bindContinuation {n : Nat} (R : Fin n → τ)
    {Γ : VCtx τ} {L K : LCtx τ}
    {block : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn R ++ L))}
    {f : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶ J.obj (labelObj M (List.ofFn R ++ L))}
    (df : CollectiveDenotes J M Γ R L block f)
    (k : J.obj (ctxObj M Γ ⊗ labelObj M (List.ofFn R ++ L)) ⟶
      J.obj (labelObj M (List.ofFn R ++ K))) :
    let E := ctxObj M Γ
    let labels := labelObj M (List.ofFn R ++ L)
    let fst := CartesianMonoidalCategory.fst
    CollectiveDenotes J M Γ R K
      (fun i => bind J (block i) (J.map (fst E (M.obj (R i)) ▷ labels) ≫ k))
      (bind J f (J.map (fst E (finiteLabelObj M R) ▷ labels) ≫ k)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.collective_continuation J M R df k

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
