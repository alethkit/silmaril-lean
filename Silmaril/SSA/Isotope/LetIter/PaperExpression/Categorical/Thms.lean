module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Categorical.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Categorical

/-! # Agreement of loop-free expression denotations with native LetIter -/

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.PaperExpression

open LocallyNameless (Tm Derivation)
open Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} {Φ : Type v} {ν : Type w}

/-- A successful lowering from the written expression grammar is loop-free. -/
theorem loopFree_of_lowering {a : Expr Φ} {n : Nat} {t : Tm Empty Φ n}
    (lowered : a.toLetIter n = some t) : LoopFree t :=
  CategoricalProofs.loopFree_of_lowering lowered

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)
  [DecidableEq ν] [TypeFormers τ] (M : TypeModel τ V)
  [HasTy Φ τ] [InstructionModel J M Φ]

/-- With the induced distributive structure of a strong Elgot Freyd model,
the loop-free interpreter agrees with native denotation. -/
theorem denoteLoopFree_eq_denote [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) (h : LoopFree t) :
    denoteLoopFree J M d h = denote J M d :=
  CategoricalProofs.denoteLoopFree_eq_denote J M d h

/-- Agreement on the source product of slots, after comparing it with the native environment. -/
theorem denoteBoundLoopFree_eq_denote [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A) (h : LoopFree t) :
    denoteBoundLoopFree J M d h = J.map (λ_ (boundObj M β)).inv ≫ denote J M d :=
  congrArg (fun f => J.map (λ_ (boundObj M β)).inv ≫ f) (denoteLoopFree_eq_denote J M d h)

end Silmaril.Isotope.LetIter.PaperExpression
