module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Singleton.Thms

/-! # Native interfaces and their coproduct cocones in the paper quotient -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- The chosen coproduct candidate concatenates the two typed exit lists. -/
@[expose] def appendCofan (X Y : ContinuationContext Φ Γ) :
    BinaryCofan (fromNative.obj X) (fromNative.obj Y) :=
  BinaryCofan.mk (fromNative.map (X.appendInl Y)) (fromNative.map (X.appendInr Y))

/-- A singleton sum uses native coproduct tags into a single sum-typed exit. -/
@[expose] def singletonSumCofan (A B : τ) :
    BinaryCofan (fromNative.obj (ContinuationContext.single (Φ := Φ) (Γ := Γ) A))
      (fromNative.obj (ContinuationContext.single B)) :=
  let X : ContinuationContext Φ Γ := ContinuationContext.single A
  let Y : ContinuationContext Φ Γ := ContinuationContext.single B
  BinaryCofan.mk
    (fromNative.map (X.appendInl Y ≫ ContinuationContext.sumTag A B))
    (fromNative.map (X.appendInr Y ≫ ContinuationContext.sumTag A B))

end Silmaril.Isotope.LambdaSSA.Region.Paper
