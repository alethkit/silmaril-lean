module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Constructors.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Defs

/-! # Constructor argument sequencing in an opt-in Paper presentation -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing

open Silmaril Silmaril.Isotope.LambdaSSA
open UnaryReturn.Beta.Constructors
open RetainedLet (returnOnce)
open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

/-- Sequence normalizing pair or injection operands at a singleton return.
The normalizing witnesses restrict the step to the constructor β fragment.
Pair operands are evaluated left to right in their original context. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | pair {Γ : VCtx τ} {a b c d : Tm Φ} {A B : τ}
      (ha : Normalizes Γ a c A) (hb : Normalizes Γ b d B) :
      Step Γ (returnOnce (.pair a b)) (pairSequence a b) [product A B]
  | inl {Γ : VCtx τ} {a c : Tm Φ} {A B : τ} (ha : Normalizes Γ a c A) :
      Step Γ (returnOnce (.inl a)) (inlSequence a) [coprod A B]
  | inr {Γ : VCtx τ} {a c : Tm Φ} {A B : τ} (ha : Normalizes Γ a c B) :
      Step Γ (returnOnce (.inr a)) (inrSequence a) [coprod A B]

variable [HasTy Φ τ]

/-- The only extra steps are singleton unary fusion and constructor sequencing. -/
def Seed (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  UnaryReturn.Step Γ r s L ∨ Step Γ r s L

abbrev Eqv : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop :=
  Extension.Eqv Seed

abbrev TypeCategory := Extension.Singleton.TypeCategory (Seed (τ := τ) (Φ := Φ))

abbrev projection : Paper.TypeCategory (τ := τ) Φ ⥤ TypeCategory (τ := τ) (Φ := Φ) :=
  Extension.Singleton.projection Seed

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing
