module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBinaryLetBind.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BinaryLetBind.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Binding.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBinaryLetBind

/-! # Soundness and the rebuilt producer in the binary-let extension -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBinaryLetBind

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.BinaryLet (returnPair)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (returnOnce)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} {a : Tm Φ} {A B : τ}

/-- Every equation in the existing Paper relation is available in the extension. -/
theorem ofPaper (h : Paper.Eqv Γ r s L) : Eqv Γ r s L := .paper h

/-- Arbitrary exactly typed product scrutinees admit the producer equality
in the extended relation. -/
theorem returnPair_eq_returnOnce (ha : Tm.HasType Γ a (product A B)) :
    Eqv Γ (returnPair a) (returnOnce a) [product A B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBinaryLetBind.returnPair_eq_returnOnce ha

section Denotation

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The Paper model assumptions suffice for the binary-let extension. -/
theorem Eqv.sound
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    (h : Eqv Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Extension.Eqv.sound J M shared (fun e _ _ => e.denotes J M) h hr hs

end Denotation

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBinaryLetBind
