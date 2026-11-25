module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Soundness.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLet

/-! # Literal unary let in the shared paper relation -/

public section

open Silmaril
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open CfgEta.TypeCategory
open Silmaril.DeBruijn (lift)

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B : τ} {a : Tm Φ} {r : Region Φ}

/-- The retained composition for unary let is equivalent to literal let
for arbitrary typed scrutinees and arbitrary exactly typed bodies. -/
theorem literal_let (ha : Tm.HasType [X] a A) (hr : Region.HasType [A, X] r [B]) :
    Paper.Eqv [X]
      (compLSubst
        (compLSubst (fun _ => diagonal) (fun _ => whiskerLeftRegion (returnOnce a)))
        (fun _ => unpackBody r) 0)
      (.let₁ a r) [B] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLet.literal_let ha hr

section Denotation

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u₁ u₂ v₁ v₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V)
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The explicit single-bind return evaluates the actual arbitrary term,
using the existing effect-preserving branch-bind equation. -/
theorem returnOnce_denotation (ha : Tm.HasType [X] a A)
    {f : J.obj (ctxObj M [X]) ⟶ J.obj (M.obj A)} (d : Denotes J M ha f) :
    denoteSingletonRegion J M (returnOnce_typed ha).hasType =
      J.map ((λ_ (M.obj X)).inv : M.obj X ⟶ ctxObj M [X]) ≫ f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLet.returnOnce_denotation J M ha d

/-- Soundness in the existing Paper model interface for the arbitrary
scrutinee syntax equation. -/
theorem literal_let_denotation
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    (ha : Tm.HasType [X] a A) (hr : Region.HasType [A, X] r [B])
    (hp : Region.HasType [X]
      (compLSubst
        (compLSubst (fun _ => diagonal) (fun _ => whiskerLeftRegion (returnOnce a)))
        (fun _ => unpackBody r) 0) [B]) :
    denoteRegion J M hp = denoteRegion J M (.let₁ ha hr) :=
  Paper.Eqv.sound J M shared (literal_let ha hr) hp (.let₁ ha hr)

end Denotation

end Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet
