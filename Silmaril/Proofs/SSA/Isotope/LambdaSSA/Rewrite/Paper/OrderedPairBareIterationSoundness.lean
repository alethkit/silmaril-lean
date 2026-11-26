module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms

/-! # Denotational soundness of binding the iteration dispatcher scrutinee -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBareIterationSoundness

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher (denote_weakenCapture)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel case_bind_value)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {A B : τ} {a : Tm Φ}
  {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
theorem denote_dispatch_bind (ha : Tm.HasType Γ a (coprod B A)) :
    denoteRegion J M (.let₁ ha
      (SyntacticCategory.iterationDispatch_valueBranches (Φ := Φ) A B).hasType) =
    denoteRegion J M (.case ha (.br (ℓ := 1) rfl (.var (i := 0) rfl))
      (.br (ℓ := 0) rfl (.var (i := 0) rfl)) : HasType Γ _ [A, B]) := by
  let S := coprod B A
  have hs := Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At (S :: Γ) 0 S)
  have hd := denote_spec J M ha
  have hl : HasType (B :: Γ) (.br 1 (.var 0) : Region Φ) [A, B] := .br (ℓ := 1) rfl (.var (i := 0) rfl)
  have hr : HasType (A :: Γ) (.br 0 (.var 0) : Region Φ) [A, B] := .br (ℓ := 0) rfl (.var (i := 0) rfl)
  have hlw := hl.renameVars ((Ren.wk Γ S).lift B)
  have hrw := hr.renameVars ((Ren.wk Γ S).lift A)
  have hc := RegionDenotes.case hs (denoteRegion_spec J M hlw) (denoteRegion_spec J M hrw)
  rw [← (RegionDenotes.let₁ hd hc).eq_denote J M,
    ← (RegionDenotes.case hd (denoteRegion_spec J M hl) (denoteRegion_spec J M hr)).eq_denote J M,
    denote_weakenCapture M J (B := S) hl, denote_weakenCapture M J (B := S) hr, ← J.map_comp]
  change _ = caseWithContext J (denote J M ha ≫ J.map (M.coprodIso B A).hom)
    (denoteRegion J M hl) (denoteRegion J M hr)
  exact (case_bind_value J (denote J M ha) (M.coprodIso B A).hom
    (denoteRegion J M hl) (denoteRegion J M hr)).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBareIterationSoundness
