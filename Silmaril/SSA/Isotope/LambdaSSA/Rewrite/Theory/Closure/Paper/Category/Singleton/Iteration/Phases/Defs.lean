module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Defs

/-! # Phases of a state type and the map forgetting the phase -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- `k + 1` phases of the state `A`: the right-nested sum `A + (A + (… + A))`. -/
def phaseType (A : τ) : Nat → τ
  | 0 => A
  | k + 1 => Silmaril.coprod A (phaseType A k)

/-- Forget the phase. On one phase it is the identity. On more it is case
analysis on the exact sum with the identity on the first summand. -/
noncomputable def phaseFold (A : τ) : (k : Nat) → (ofType (Φ := Φ) (phaseType A k) ⟶ ofType A)
  | 0 => 𝟙 _
  | k + 1 => (sumIso A (phaseType A k)).hom ≫ coprod.desc (𝟙 _) (phaseFold A k)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
