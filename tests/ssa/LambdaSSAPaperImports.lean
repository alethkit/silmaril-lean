module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Feedback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Coproducts.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Thms

open CategoryTheory Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region.Paper

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

example : (fromNative (Φ := Φ) (Γ := Γ)).Full :=
  inferInstance

example (X Y : Region.ContinuationContext Φ Γ)
    (f : fromNative.obj X ⟶ fromNative.obj (X.append Y)) :
    fromNative.obj X ⟶ fromNative.obj Y :=
  feedback f

#check appendIsColimit
#check singletonSumIsColimit
#check TypeCategory.sumCofanIsColimit
