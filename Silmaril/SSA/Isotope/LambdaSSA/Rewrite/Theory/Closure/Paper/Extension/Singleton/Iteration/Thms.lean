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

/-- Iterate an exact return-or-repeat sum in the extended singleton quotient. -/
@[expose] def iterateSum (f : ofType Seed A ⟶ ofType Seed (Silmaril.coprod B A)) :
    ofType Seed A ⟶ ofType Seed B :=
  Quot.liftOn f (fun g => (projection Seed).map (Paper.TypeCategory.iterateSum g))
    (fun _ _ h => iterateSum_map_congr Seed (Quot.sound h))

/-- The descended iterator computes canonical Paper feedback on a representative. -/
theorem iterateSum_map (f : Paper.TypeCategory.ofType (Φ := Φ) A ⟶
    Paper.TypeCategory.ofType (Silmaril.coprod B A)) :
    iterateSum Seed ((projection Seed).map f) =
      (projection Seed).map (Paper.TypeCategory.iterateSum f) := rfl

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
