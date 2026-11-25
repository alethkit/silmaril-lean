module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Categorical.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Defs

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.PaperExpression.CategoricalProofs

open LocallyNameless (Tm Derivation)
open Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} {Φ : Type v} {ν : Type w}

public theorem loopFree_of_lowering {a : Expr Φ} {n : Nat} {t : Tm Empty Φ n}
    (lowered : a.toLetIter n = some t) : LoopFree t := by
  induction a generalizing n with
  | var i =>
    by_cases hi : i < n
    · simp only [Expr.toLetIter, dite_eq_left hi, Option.some.injEq] at lowered
      cases lowered
      trivial
    · simp [Expr.toLetIter, hi] at lowered
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih =>
    simp only [Expr.toLetIter, Option.map_eq_some_iff] at lowered
    obtain ⟨arg, loweredArg, rfl⟩ := lowered
    exact ih (t := arg) loweredArg
  | let₁ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | let₂ _ _ ih₁ ih₂ =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
    obtain ⟨l, loweredL, r, loweredR, rfl⟩ := lowered
    exact ⟨ih₁ loweredL, ih₂ loweredR⟩
  | case _ _ _ ih₁ ih₂ ih₃ =>
    simp only [Expr.toLetIter, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
    obtain ⟨a, loweredA, l, loweredL, r, loweredR, rfl⟩ := lowered
    exact ⟨ih₁ loweredA, ih₂ loweredL, ih₃ loweredR⟩
  | unit =>
    cases Option.some.inj lowered
    trivial

section Agreement

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)
  [DecidableEq ν] [TypeFormers τ] (M : TypeModel τ V)
  [HasTy Φ τ] [InstructionModel J M Φ]

/-- When iteration is present, the restricted interpreter agrees with the
production native interpreter on every loop-free derivation. -/
public theorem denoteLoopFree_eq_denote [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) (h : LoopFree t) :
    denoteLoopFree J M d h = denote J M d := by
  induction d with
  | fv _ | bv | unit => rfl
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
    simp only [denoteLoopFree, denote, ih h]
  | let₁ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | let₂ _ _ ih₁ ih₂ =>
    simp only [denoteLoopFree, denote, ih₁ h.1, ih₂ h.2]
  | case _ _ _ ih₁ ih₂ ih₃ =>
    simp only [denoteLoopFree, denote, ih₁ h.1, ih₂ h.2.1, ih₃ h.2.2]
  | iter => exact False.elim h

end Agreement

end Silmaril.Isotope.LetIter.PaperExpression.CategoricalProofs
