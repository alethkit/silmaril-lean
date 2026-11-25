module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionIteration

/-! # Feedback congruence in the opt-in singleton quotient -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) {A B : τ}

/-- The literal one-block loop respects projected equality at the same state and result types. -/
theorem iterateSum_map_congr {f g : Paper.TypeCategory.ofType (Φ := Φ) A ⟶
    Paper.TypeCategory.ofType (Silmaril.coprod B A)}
    (h : (projection Seed).map f = (projection Seed).map g) :
    (projection Seed).map (Paper.TypeCategory.iterateSum f) =
      (projection Seed).map (Paper.TypeCategory.iterateSum g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionIteration.iterateSum_map_congr
    Seed h

/-- The same congruence at the chosen categorical coproduct. -/
theorem iterate_map_congr {f g : Paper.TypeCategory.ofType (Φ := Φ) A ⟶
    Paper.TypeCategory.ofType B ⨿ Paper.TypeCategory.ofType A}
    (h : (projection Seed).map f = (projection Seed).map g) :
    (projection Seed).map (Paper.TypeCategory.iterate f) =
      (projection Seed).map (Paper.TypeCategory.iterate g) := by
  apply iterateSum_map_congr Seed
  simp only [Functor.map_comp, h]

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
