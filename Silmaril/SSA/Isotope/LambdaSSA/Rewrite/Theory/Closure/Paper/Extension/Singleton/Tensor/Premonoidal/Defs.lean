module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Coherence.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Unit.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Defs

/-! # Guarded structural arrows in contextual singleton quotients -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (leftUnitProjection rightUnitProjection)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "P" => projection Seed
local notation "U" => (Silmaril.unit : τ)
local notation "Obj" => ofType (Φ := Φ) Seed
local notation "T" => tensorObj Seed
local notation "L" => whiskerLeft Seed
local notation "R" => whiskerRight Seed

abbrev associateIso (A B C : Q) : T (T A B) C ≅ T A (T B C) :=
  (P).mapIso (Paper.TypeCategory.associateIso (show τ from A.as) (show τ from B.as) (show τ from C.as))

abbrev braidIso (A B : Q) : T A B ≅ T B A :=
  (P).mapIso (Paper.TypeCategory.braidIso (show τ from A.as) (show τ from B.as))

abbrev unitProjectionLeft (X : Q) : T (Obj U) X ⟶ X := (P).map (leftUnitProjection (show τ from X.as))
abbrev unitProjectionRight (X : Q) : T X (Obj U) ⟶ X := (P).map (rightUnitProjection (show τ from X.as))

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
