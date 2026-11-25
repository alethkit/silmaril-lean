module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Bind.Defs

/-! # Typed call-by-value flattening of straight-line source expressions -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten

universe u r

variable {α Φ : Type u} (S : Signature α Φ)

abbrev argSort {f : Φ} {k : Nat} (h : S.arity f = k) (i : Fin k) : α :=
  S.arg f (i.cast h.symm)

/-- All arguments have atomic sorts. A let may sequence either a pure
initializer or one containing visible calls. Unary and binary application
construct the actual source argument tuple from their subexpressions. -/
inductive Program : {n : Nat} → (Fin n → α) → α → Type (u + 1)
  | tree {n : Nat} {slots : Fin n → α} {c : α} : Tree S slots c → Program slots c
  | let1 {n : Nat} {slots : Fin n → α} {a c : α} :
      Program slots a → Program (extendSorts a slots) c → Program slots c
  | request {n : Nat} {slots : Fin n → α} (f : Φ) :
      Args S slots f → Program slots (S.out f)
  | unary {n : Nat} {slots : Fin n → α} (f : Φ) (h : S.arity f = 1) :
      Program slots (argSort S h 0) → Program slots (S.out f)
  | binary {n : Nat} {slots : Fin n → α} (f : Φ) (h : S.arity f = 2) :
      Program slots (argSort S h 0) → Program slots (argSort S h 1) → Program slots (S.out f)

namespace Program

def source : {n : Nat} → {slots : Fin n → α} → {c : α} → Program S slots c → Expr Φ
  | _, _, _, .tree p => p.source
  | _, _, _, .let1 p q => .let₁ (source p) (source q)
  | _, _, _, .request f args => (Tree.op f args).source
  | _, _, _, .unary f _ p => .op f (.pair (source p) .unit)
  | _, _, _, .binary f _ p q => .op f (.pair (source p) (.pair (source q) .unit))

variable {ε : Type r} [HasEff Φ ε] [Preorder ε] [Bot ε]

def WellTyped (e : ε) : {n : Nat} → {slots : Fin n → α} → {c : α} → Program S slots c → Prop
  | _, _, _, .tree p => DeclaredPure (ε := ε) S p
  | _, _, _, .let1 p q => WellTyped e p ∧ WellTyped e q
  | _, _, _, .request f args => instrEff f ≤ e ∧ ∀ i, DeclaredPure (ε := ε) S (args i)
  | _, _, _, .unary f _ p => instrEff f ≤ e ∧ WellTyped e p
  | _, _, _, .binary f _ p q => instrEff f ≤ e ∧ WellTyped e p ∧ WellTyped e q

end Program

section Arguments

variable {n : Nat} {slots : Fin n → α}

/-- Transport a finite tuple across a proof of its arity. -/
def argsAtArity {m k : Nat} {as : Fin m → α} (h : m = k)
    (xs : (i : Fin k) → Tree S slots (as (i.cast h.symm))) :
    (i : Fin m) → Tree S slots (as i) :=
  match h with
  | rfl => xs

def unaryArgs {f : Φ} (h : S.arity f = 1) (p : Tree S slots (argSort S h 0)) :
    Args S slots f :=
  argsAtArity S h (Fin.cases (motive := fun i => Tree S slots (argSort S h i))
    p fun i => i.elim0)

def binaryArgs {f : Φ} (h : S.arity f = 2)
    (p : Tree S slots (argSort S h 0)) (q : Tree S slots (argSort S h 1)) :
    Args S slots f :=
  argsAtArity S h (Fin.cases (motive := fun i => Tree S slots (argSort S h i))
    p (Fin.cases q fun i => i.elim0))

end Arguments

section Compiler

variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {n : Nat} {slots : Fin n → α}

/-- A pure primitive builds a tree. An effectful primitive emits a call
and returns the new response. -/
noncomputable def emit (f : Φ) (args : Args S slots f) : Sequence S (S.out f) slots := by
  classical
  exact if IsPure (⊥ : ε) f then .ret (.op f args) else .call f args (.ret (.var 0))

noncomputable def unaryTail (f : Φ) (h : S.arity f = 1) :
    Sequence S (S.out f) (extendSorts (argSort S h 0) slots) :=
  emit (ε := ε) S f (unaryArgs S h (.var 0))

noncomputable def binaryTail (f : Φ) (h : S.arity f = 2) :
    Sequence S (S.out f) (extendSorts (argSort S h 1) (extendSorts (argSort S h 0) slots)) :=
  emit (ε := ε) S f (binaryArgs S h (.var (0 : Fin (n + 1)).succ) (.var 0))

/-- Flatten left to right. Each argument is evaluated before the primitive,
and the second argument retains the first argument's value. -/
noncomputable def compile : {n : Nat} → {slots : Fin n → α} → {c : α} →
    Program S slots c → Sequence S c slots
  | _, _, _, .tree p => .ret p
  | _, _, _, .let1 p q => Sequence.bind S (compile p) (compile q)
  | _, _, _, .request f args => emit (ε := ε) S f args
  | _, _, _, .unary f h p => Sequence.bind S (compile p) (unaryTail (ε := ε) S f h)
  | _, _, _, .binary f h p q =>
      Sequence.bind S (compile p)
        (Sequence.bind S (Sequence.weaken S (argSort S h 0) (compile q)) (binaryTail (ε := ε) S f h))

end Compiler

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten
