module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Defs

/-! # Pure substitution and sequencing for normalized calls -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence

universe u

variable {α Φ : Type u} (S : Signature α Φ) {a c : α}
  {n m : Nat} {slots : Fin n → α} {target : Fin m → α}

abbrev TreeSubst (slots : Fin n → α) (target : Fin m → α) :=
  (i : Fin n) → Tree S target (slots i)

def liftSubst (σ : TreeSubst S slots target) (a : α) :
    TreeSubst S (extendSorts a slots) (extendSorts a target) :=
  Fin.cases (motive := fun i => Tree S (extendSorts a target) (extendSorts a slots i))
    (.var 0) fun i => (σ i).interpret S (Tree S (extendSorts a target)) Tree.op
      (fun j => .var j.succ)

/-- Substitute pure trees for ambient variables, lifting below each response. -/
def subst : {n m : Nat} → {slots : Fin n → α} → {target : Fin m → α} →
    Sequence S c slots → TreeSubst S slots target → Sequence S c target
  | _, _, _, _, .ret p, σ => .ret (p.interpret S _ Tree.op σ)
  | _, _, _, _, .call f args next, σ =>
      .call f (fun i => (args i).interpret S _ Tree.op σ) (subst next (liftSubst S σ (S.out f)))

def subst0 (v : Tree S slots a) : TreeSubst S (extendSorts a slots) slots :=
  extendValues S slots v Tree.var

def liftAmbientSubst (a x : α) :
    TreeSubst S (extendSorts a slots) (extendSorts a (extendSorts x slots)) :=
  Fin.cases (motive := fun i =>
    Tree S (extendSorts a (extendSorts x slots)) (extendSorts a slots i))
    (.var 0) fun i => .var i.succ.succ

def weaken (x : α) (p : Sequence S c slots) : Sequence S c (extendSorts x slots) :=
  subst S p (fun i => .var i.succ)

/-- Run the first sequence and substitute its pure return into the body. -/
def bind : {n : Nat} → {slots : Fin n → α} →
    Sequence S a slots → Sequence S c (extendSorts a slots) → Sequence S c slots
  | _, _, .ret v, q => subst S q (subst0 S v)
  | _, _, .call f args next, q =>
      .call f args (bind next (subst S q (liftAmbientSubst S a (S.out f))))

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence
