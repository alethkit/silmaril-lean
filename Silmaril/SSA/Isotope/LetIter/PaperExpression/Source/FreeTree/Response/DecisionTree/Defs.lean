module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Defs

/-! # Finite decision trees over pure sum inputs -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree

universe u w

variable {α : Type u} {ε : Type w} [Bot ε]

/-- A split replaces one sum slot by its atomic payload in place. Every leaf
has an atomic context. A branch may choose its next split independently. -/
inductive Shape : EffectCtx (Ty α) ε → Type (max u w) where
  | leaf {Γ : EffectCtx (Ty α) ε} (slots : Fin Γ.length → α) :
      (∀ i, (Γ.get i).1 = .base (slots i)) → Shape Γ
  | split {Γ : EffectCtx (Ty α) ε} (i : Fin Γ.length) {x y : α} :
      (Γ.get i).1 = .coprod (.base x) (.base y) →
      Shape (SumSplit.branchCtx Γ i (.base x)) → Shape (SumSplit.branchCtx Γ i (.base y)) → Shape Γ

variable {Φ : Type u} (S : Signature α Φ) (c : α)

/-- A decision tree assigns a straight-line program to every leaf of its
shape, in the context of all payloads selected along that path. -/
inductive Program : {Γ : EffectCtx (Ty α) ε} → Shape Γ → Type (max (u + 1) w) where
  | leaf {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}
      {hs : ∀ i, (Γ.get i).1 = .base (slots i)} :
      Flatten.Program S slots c → Program (Shape.leaf slots hs)
  | split {Γ : EffectCtx (Ty α) ε} (i : Fin Γ.length) {x y : α}
      {ht : (Γ.get i).1 = .coprod (.base x) (.base y)}
      {left : Shape (SumSplit.branchCtx Γ i (.base x))} {right : Shape (SumSplit.branchCtx Γ i (.base y))} :
      Program left → Program right → Program (Shape.split i ht left right)

namespace Program

variable {c : α}

/-- Render the tests as source cases, moving each replaced slot to the new
payload binder while preserving all the other variables. -/
def source : {Γ : EffectCtx (Ty α) ε} → {shape : Shape Γ} → Program S c shape → Expr Φ
  | _, _, .leaf p => p.source
  | _, _, .split i l r => SumSplit.caseArms i (source l) (source r)

variable [HasEff Φ ε] [Preorder ε]

/-- Every straight-line leaf is checked at the same supplied source bound. -/
def WellTyped (e : ε) : {Γ : EffectCtx (Ty α) ε} → {shape : Shape Γ} → Program S c shape → Prop
  | _, _, .leaf p => Flatten.Program.WellTyped S e p
  | _, _, .split _ l r => WellTyped e l ∧ WellTyped e r

end Program

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree
