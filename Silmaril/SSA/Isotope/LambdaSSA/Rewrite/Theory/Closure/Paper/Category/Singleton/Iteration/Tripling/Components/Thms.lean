module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Unit.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTripling
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTriplingProjection

/-! # Tripling on retained Bit by native block elimination -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ
local notation "T" => BitState (τ := τ) (Φ := Φ)

/-- Either tag may take any recursive or outward route. Reset absorption
only concerns the two Unit payloads of the Bit. -/
theorem iterate_triple {B : P} (g : T ⟶ B ⨿ T)
    (input : resetPayloads ≫ g = g) (output : g ≫ coprod.map (𝟙 B) resetPayloads = g) :
    iterate (thenOnRepeat g (thenOnRepeat g g)) = iterate g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTripling.iterate_triple g input output

/-- A mixed Bit round with literal Unit payloads satisfies tripling in standard Paper. -/
theorem iterate_normalize {B : P} (g : T ⟶ B ⨿ T) :
    iterate (thenOnRepeat (normalize g) (thenOnRepeat (normalize g) (normalize g))) =
      iterate (normalize g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTripling.iterate_normalize g

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "Bit" => ofType Seed (Silmaril.coprod (Silmaril.unit : τ) Silmaril.unit)

/-- Unit η lets the native component proof apply to every quotient round
at the exact Bit state, including rounds with mixed effectful recurrence. -/
theorem triple_step_bit
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    {B : Q} (g : Bit ⟶ B ⨿ Bit) :
    iterateChosen Seed (triple g) = iterateChosen Seed g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTriplingProjection.triple_step_bit
    Seed includeUnit g

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle
