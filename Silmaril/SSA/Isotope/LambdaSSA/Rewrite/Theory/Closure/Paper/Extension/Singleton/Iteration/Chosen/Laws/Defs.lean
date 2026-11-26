module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Defs
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Transport a Paper feedback step to the quotient's chosen coproduct -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "P" => Paper.TypeCategory (τ := τ) Φ
local notation "proj" => projection Seed
local notation "c" => PreservesColimitPair.iso (proj)

/-- Project an ordinary step and compare its result with the chosen quotient sum. -/
noncomputable abbrev projectStep {X Y : P} (f : X ⟶ Y ⨿ X) :
    (proj).obj X ⟶ (proj).obj Y ⨿ (proj).obj X :=
  (proj).map f ≫ (c Y X).inv

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
