module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Defs

/-! # Finite sequences of normalized response-bearing calls -/

@[expose] public section

open Silmaril Silmaril.Isotope Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response

universe u r

variable {α Φ : Type u} (S : Signature α Φ)

/-- A pure return or a normalized request followed by a sequence in the
scope extended by its atomic response. -/
inductive Sequence (result : α) : {n : Nat} → (Fin n → α) → Type (u + 1)
  | ret {n : Nat} {slots : Fin n → α} : Tree S slots result → Sequence result slots
  | call {n : Nat} {slots : Fin n → α} (f : Φ) :
      Args S slots f → Sequence result (extendSorts (S.out f) slots) → Sequence result slots

namespace Sequence

variable {c : α}

def source : {n : Nat} → {slots : Fin n → α} → Sequence S c slots → Expr Φ
  | _, _, .ret p => p.source
  | _, _, .call f args next => .let₁ (Tree.op f args).source (source next)

def native : {n : Nat} → {slots : Fin n → α} → Sequence S c slots → Tm Empty Φ n
  | _, _, .ret p => p.native
  | _, _, .call f args next => .let₁ (Tree.op f args).native (native next)

variable {ε : Type r} [HasEff Φ ε] [Preorder ε] [Bot ε]

/-- Every call is non-bottom and permitted by the same original bound, while
all arguments and the final return are declared pure. -/
def WellTyped (e : ε) : {n : Nat} → {slots : Fin n → α} → Sequence S c slots → Prop
  | _, _, .ret p => DeclaredPure (ε := ε) S p
  | _, _, .call f args next =>
      (∀ i, DeclaredPure (ε := ε) S (args i)) ∧
        ¬ IsPure (⊥ : ε) f ∧ instrEff f ≤ e ∧ WellTyped e next

variable {m : Nat} (modelSlots : Fin m → α)

/-- Interpret atomic requests through a response-type-preserving event injection. -/
noncomputable def denoteWith {E : Type (u + 1) → Type (u + 1)}
    (event : (f : Φ) → Args S modelSlots f → E (Tree S modelSlots (S.out f))) :
    {n : Nat} → {slots : Fin n → α} → Sequence S c slots →
      ((i : Fin n) → Tree S modelSlots (slots i)) → ITree.Tree E (Atom S modelSlots c)
  | _, _, .ret p, vars => ITree.ret ⟨p.interpret S (Tree S modelSlots) Tree.op vars⟩
  | _, _, .call f args next, vars =>
      ITree.vis (event f (fun i => (args i).interpret S (Tree S modelSlots) Tree.op vars))
        (fun r => denoteWith event next (extendValues S modelSlots r vars))

/-- Evaluate the normalized sequence in the response model at a sorted valuation. -/
noncomputable def denote {n : Nat} {slots : Fin n → α}
    (p : Sequence S c slots) (vars : (i : Fin n) → Tree S modelSlots (slots i)) :
    ITree.Tree (Event S modelSlots) (Atom S modelSlots c) :=
  denoteWith S modelSlots Event.call p vars

end Sequence

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response
