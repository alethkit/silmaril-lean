module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Singleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Coproducts.Thms

/-! # Native sum β and η for a pair of singleton interfaces -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open ContinuationContext (single sumCase sumTagRegion)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

theorem sumTag_valueFamily (A B : τ) :
    LSubst.ValueFamily Γ [A, B] [Silmaril.coprod A B] (sumTagRegion (Φ := Φ)) := by
  intro i D hi
  cases i with
  | zero =>
    have e : some A = some D := hi
    cases e
    exact .br rfl (.inl (.var rfl))
  | succ i =>
    cases i with
    | zero =>
      have e : some B = some D := hi
      cases e
      exact .br rfl (.inr (.var rfl))
    | succ i => simp [At] at hi

@[expose] def sumTag (A B : τ) :
    (single A : ContinuationContext Φ Γ).append (single B) ⟶ single (Silmaril.coprod A B) :=
  ContinuationFamily.toHom ⟨sumTagRegion, sumTag_valueFamily A B⟩

theorem sumTag_sumCase (A B : τ) :
    sumTag (Φ := Φ) (Γ := Γ) A B ≫ sumCase A B = 𝟙 ((single A).append (single B)) := by
  apply ContinuationFamily.toHom_eq_iff.mpr
  intro i D hi
  cases i with
  | zero =>
    have e : some A = some D := hi
    cases e
    have hleft : Region.HasType (A :: A :: Γ) (.br 0 (.var 0) : Region Φ) [A, B] := .br rfl (.var rfl)
    have hright : Region.HasType (B :: A :: Γ) (.br 1 (.var 0) : Region Φ) [A, B] := .br rfl (.var rfl)
    exact (SubstitutionEquiv.base (.caseInl (.var rfl) hleft hright)).trans (.letValue (.var rfl) hleft)
  | succ i =>
    cases i with
    | zero =>
      have e : some B = some D := hi
      cases e
      have hleft : Region.HasType (A :: B :: Γ) (.br 0 (.var 0) : Region Φ) [A, B] := .br rfl (.var rfl)
      have hright : Region.HasType (B :: B :: Γ) (.br 1 (.var 0) : Region Φ) [A, B] := .br rfl (.var rfl)
      exact (SubstitutionEquiv.base (.caseInr (.var rfl) hleft hright)).trans (.letValue (.var rfl) hright)
    | succ i => simp [At, ContinuationContext.append, single] at hi

theorem sumCase_sumTag (A B : τ) :
    sumCase (Φ := Φ) (Γ := Γ) A B ≫ sumTag A B = 𝟙 (single (Silmaril.coprod A B)) := by
  apply ContinuationFamily.toHom_eq_iff.mpr
  intro i D hi
  cases i with
  | zero =>
    have e : some (Silmaril.coprod A B) = some D := hi
    cases e
    have hbody : Region.HasType (Silmaril.coprod A B :: Silmaril.coprod A B :: Γ)
        (.br 0 (.var 0) : Region Φ) [Silmaril.coprod A B] := .br rfl (.var rfl)
    exact .caseValue (A := A) (B := B) (.var (i := 0) rfl) hbody
  | succ i => simp [At, single] at hi

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
