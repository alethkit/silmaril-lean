module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall.Defs

/-! # Finite mixed request trees -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed

open SumCall (SumSignature SumArgs treeSource treeNative)

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)

/-- A finite request tree can continue after an atomic reply or branch on a
sum reply. Each child binds its payload ahead of the existing variables. -/
inductive Program (result : α) : {n : Nat} → (Fin n → α) → Type (u + 1)
  | ret {n : Nat} {slots : Fin n → α} : Tree S slots result → Program result slots
  | atom {n : Nat} {slots : Fin n → α} (f : Φ) :
      Args S slots f → Program result (extendSorts (S.out f) slots) → Program result slots
  | sum {n : Nat} {slots : Fin n → α} (g : Ψ) :
      SumArgs S T slots g → Program result (extendSorts (T.left g) slots) →
        Program result (extendSorts (T.right g) slots) → Program result slots

variable {c : α}

/-- Include any finite atomic sequence in the mixed signature. -/
def ofSequence : {n : Nat} → {slots : Fin n → α} → Sequence S c slots → Program S T c slots
  | _, _, .ret p => .ret p
  | _, _, .call f args next => .atom f args (ofSequence next)

/-- Include the case on a single sum call with straight-line arms. -/
def ofSumCall {n : Nat} {slots : Fin n → α} (p : SumCall.Program S T slots c) :
    Program S T c slots :=
  .sum p.op p.args (ofSequence S T p.left) (ofSequence S T p.right)

namespace Program

def source : {n : Nat} → {slots : Fin n → α} → Program S T c slots → Expr (Φ ⊕ Ψ)
  | _, _, .ret p => treeSource S p
  | _, _, .atom f args next =>
      .let₁ (.op (.inl f) (sourceTuple (S.arity f) (fun i => treeSource S (args i)))) (source next)
  | _, _, .sum g args left right =>
      .case (.op (.inr g) (sourceTuple (T.arity g) (fun i => treeSource S (args i))))
        (source left) (source right)

def native : {n : Nat} → {slots : Fin n → α} → Program S T c slots → Tm Empty (Φ ⊕ Ψ) n
  | _, _, .ret p => treeNative S p
  | _, _, .atom f args next =>
      .let₁ (.op (.inl f) (nativeTuple (S.arity f) (fun i => treeNative S (args i)))) (native next)
  | _, _, .sum g args left right =>
      .case (.op (.inr g) (nativeTuple (T.arity g) (fun i => treeNative S (args i))))
        (native left) (native right)

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [Preorder ε] [Bot ε]

/-- Every subtree is checked at the same supplied effect bound. Atomic
requests are visible, and all request arguments and the final return are pure. -/
def WellTyped (e : ε) : {n : Nat} → {slots : Fin n → α} → Program S T c slots → Prop
  | _, _, .ret p => DeclaredPure (ε := ε) S p
  | _, _, .atom f args next =>
      (∀ i, DeclaredPure (ε := ε) S (args i)) ∧ ¬ IsPure (⊥ : ε) f ∧
        instrEff f ≤ e ∧ WellTyped e next
  | _, _, .sum g args left right =>
      (∀ i, DeclaredPure (ε := ε) S (args i)) ∧ instrEff g ≤ e ∧
        WellTyped e left ∧ WellTyped e right

variable {m : Nat} (modelSlots : Fin m → α)

/-- Each request emits one visible event; its actual reply supplies the new
value at index zero in exactly the selected subtree. -/
noncomputable def denote : {n : Nat} → {slots : Fin n → α} → Program S T c slots →
    ((i : Fin n) → Tree S modelSlots (slots i)) →
      ITree.Tree (SumCall.Event S T modelSlots) (Atom S modelSlots c)
  | _, _, .ret p, vars => ITree.ret ⟨p.interpret S (Tree S modelSlots) Tree.op vars⟩
  | _, _, .atom f args next, vars =>
      ITree.vis (.atom f (fun i => (args i).interpret S (Tree S modelSlots) Tree.op vars))
        (fun r => denote next (extendValues S modelSlots r vars))
  | _, _, .sum g args left right, vars =>
      ITree.vis (.sum g (fun i => (args i).interpret S (Tree S modelSlots) Tree.op vars))
        (fun
          | .inl r => denote left (extendValues S modelSlots r vars)
          | .inr r => denote right (extendValues S modelSlots r vars))

end Program

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed
