module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Defs

/-! # Mixed requests with compound pure return values -/

@[expose] public section

open Silmaril
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization (Value)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature SumArgs treeSource)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {n : Nat} {slots : Fin n → α}

/-- Render a constructor value in the mixed instruction signature. -/
def valueSource : {A : Ty α} → Value S slots A → Expr (Φ ⊕ Ψ)
  | _, .tree t => treeSource S t
  | _, .unit => .unit
  | _, .pair p q => .pair (valueSource p) (valueSource q)
  | _, .inl p => .inl (valueSource p)
  | _, .inr q => .inr (valueSource q)

/-- A mixed request tree with pure, possibly compound return values. Only
atomic payload variables enter the context at a request. -/
inductive Code (A : Ty α) : {n : Nat} → (Fin n → α) → Type (u + 1)
  | ret {n : Nat} {slots : Fin n → α} : Value S slots A → Code A slots
  | atom {n : Nat} {slots : Fin n → α} (f : Φ) :
      Args S slots f → Code A (extendSorts (S.out f) slots) → Code A slots
  | sum {n : Nat} {slots : Fin n → α} (g : Ψ) :
      SumArgs S T slots g → Code A (extendSorts (T.left g) slots) →
        Code A (extendSorts (T.right g) slots) → Code A slots

namespace Code

variable {A : Ty α} {c : α}

def source : {n : Nat} → {slots : Fin n → α} → Code S T A slots → Expr (Φ ⊕ Ψ)
  | _, _, .ret v => valueSource S v
  | _, _, .atom f args next =>
      .let₁ (.op (.inl f) (sourceTuple (S.arity f) (fun i => treeSource S (args i)))) (source next)
  | _, _, .sum g args left right =>
      .case (.op (.inr g) (sourceTuple (T.arity g) (fun i => treeSource S (args i))))
        (source left) (source right)

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [Preorder ε] [Bot ε]

def WellTyped (e : ε) : {n : Nat} → {slots : Fin n → α} → Code S T A slots → Prop
  | _, _, .ret v => v.Pure (ε := ε) S
  | _, _, .atom f args next =>
      (∀ i, DeclaredPure (ε := ε) S (args i)) ∧ ¬ IsPure (⊥ : ε) f ∧
        instrEff f ≤ e ∧ WellTyped e next
  | _, _, .sum g args left right =>
      (∀ i, DeclaredPure (ε := ε) S (args i)) ∧ instrEff g ≤ e ∧
        WellTyped e left ∧ WellTyped e right

/-- At an atomic result, the intermediate language is the existing mixed
reflection grammar. -/
def toMixed : {n : Nat} → {slots : Fin n → α} → Code S T (.base c) slots → Mixed.Program S T c slots
  | _, _, .ret (.tree t) => .ret t
  | _, _, .atom f args next => .atom f args (toMixed next)
  | _, _, .sum g args left right => .sum g args (toMixed left) (toMixed right)

end Code

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written
