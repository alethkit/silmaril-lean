module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Singleton.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.CategoryCoproducts

/-! # Coproducts of exit interfaces in the CFG η quotient -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- The interface with no labels is initial in the enlarged quotient. -/
noncomputable def emptyIsInitial : IsInitial ((fromNative (Φ := Φ) (Γ := Γ)).obj ContinuationContext.empty) :=
  by exact Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.emptyIsInitial

/-- The images of the two label inclusions exhibit concatenation as a coproduct. -/
noncomputable def appendIsColimit (X Y : ContinuationContext Φ Γ) :
    IsColimit (BinaryCofan.mk (fromNative.map (X.appendInl Y)) (fromNative.map (X.appendInr Y))) :=
  by exact Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.appendIsColimit X Y

/-- Tagging two singleton interfaces gives a coproduct with one sum-typed exit. -/
noncomputable def singletonSumIsColimit (A B : τ) :
    let X : ContinuationContext Φ Γ := ContinuationContext.single A
    let Y : ContinuationContext Φ Γ := ContinuationContext.single B
    IsColimit (BinaryCofan.mk
      (fromNative.map (X.appendInl Y ≫ ContinuationContext.sumTag A B))
      (fromNative.map (X.appendInr Y ≫ ContinuationContext.sumTag A B))) :=
  by exact Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.singletonSumIsColimit A B

/-- The empty type represents an initial singleton interface. -/
noncomputable def singletonEmptyIsInitial :
    IsInitial (fromNative.obj (ContinuationContext.single (Silmaril.empty : τ) :
      ContinuationContext Φ Γ)) :=
  emptyIsInitial.ofIso (fromNative.mapIso
    (Classical.choice ((ContinuationContext.empty : ContinuationContext Φ Γ).nonempty_packedIso)))

end Silmaril.Isotope.LambdaSSA.Region.CfgEta
