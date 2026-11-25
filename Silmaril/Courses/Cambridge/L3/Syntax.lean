module

public import Silmaril.Courses.Cambridge.L1.Syntax
public import Silmaril.Prelude.DeBruijn

/-! # Cambridge L3 abstract syntax

Sewell, *Semantics of Programming Languages* (12 February 2026), §§5.1–5.3
and §5.5, p. 78. The source is `sewell2026semantics` in `references.bib`.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3

abbrev Op := L1.Op
abbrev Loc := Nat
abbrev Var := String
abbrev Label := String

/-- Record labels are distinct and retain their source order. -/
structure RecordLabels where
  names : List Label
  distinct : names.Nodup

abbrev RecordLabels.Index (labels : RecordLabels) := Fin labels.names.length

def RecordLabels.label (labels : RecordLabels) (i : labels.Index) : Label :=
  labels.names.get i

theorem RecordLabels.eq_of_label_eq {labels : RecordLabels} {i j : labels.Index}
    (h : labels.label i = labels.label j) : i = j :=
  Fin.ext (labels.distinct.eq_of_getElem_eq i.isLt j.isLt h)

inductive Ty where
  | int
  | bool
  | unit
  | arr (domain codomain : Ty)
  | prod (left right : Ty)
  | sum (left right : Ty)
  | record (labels : RecordLabels) (fields : labels.Index → Ty)
  | ref (contents : Ty)

/-- Bound occurrences use de Bruijn indices. The parameter of `letRecFun`
is at index zero and the recursive name at index one in its function body.
Each match branch binds its own payload at index zero. -/
inductive Expr where
  | int (value : Int)
  | bool (value : Bool)
  | binary (left : Expr) (op : Op) (right : Expr)
  | cond (test yes no : Expr)
  | assign (lhs rhs : Expr)
  | deref (reference : Expr)
  | ref (value : Expr)
  | loc (address : Loc)
  | skip
  | seq (left right : Expr)
  | loop (test body : Expr)
  | bvar (index : Nat)
  | fvar (name : Var)
  | lam (domain : Ty) (body : Expr)
  | app (function argument : Expr)
  | letE (type : Ty) (value body : Expr)
  | letRecFun (domain codomain : Ty) (functionBody body : Expr)
  | pair (left right : Expr)
  | fst (pair : Expr)
  | snd (pair : Expr)
  | inl (payload : Expr) (sumType : Ty)
  | inr (payload : Expr) (sumType : Ty)
  | matchSum (scrutinee : Expr) (leftType : Ty) (left : Expr) (rightType : Ty) (right : Expr)
  | record (labels : RecordLabels) (fields : labels.Index → Expr)
  | project (record : Expr) (label : Label)

def Expr.rename (ρ : Nat → Nat) : Expr → Expr
  | .int n => .int n
  | .bool b => .bool b
  | .binary left op right => .binary (left.rename ρ) op (right.rename ρ)
  | .cond test yes no => .cond (test.rename ρ) (yes.rename ρ) (no.rename ρ)
  | .assign lhs rhs => .assign (lhs.rename ρ) (rhs.rename ρ)
  | .deref e => .deref (e.rename ρ)
  | .ref e => .ref (e.rename ρ)
  | .loc address => .loc address
  | .skip => .skip
  | .seq left right => .seq (left.rename ρ) (right.rename ρ)
  | .loop test body => .loop (test.rename ρ) (body.rename ρ)
  | .bvar index => .bvar (ρ index)
  | .fvar name => .fvar name
  | .lam domain body => .lam domain (body.rename (DeBruijn.lift ρ))
  | .app fn arg => .app (fn.rename ρ) (arg.rename ρ)
  | .letE type value body => .letE type (value.rename ρ) (body.rename (DeBruijn.lift ρ))
  | .letRecFun domain codomain functionBody body =>
      .letRecFun domain codomain (functionBody.rename (DeBruijn.liftN 2 ρ))
        (body.rename (DeBruijn.lift ρ))
  | .pair left right => .pair (left.rename ρ) (right.rename ρ)
  | .fst e => .fst (e.rename ρ)
  | .snd e => .snd (e.rename ρ)
  | .inl e T => .inl (e.rename ρ) T
  | .inr e T => .inr (e.rename ρ) T
  | .matchSum e A left B right =>
      .matchSum (e.rename ρ) A (left.rename (DeBruijn.lift ρ))
        B (right.rename (DeBruijn.lift ρ))
  | .record labels fields => .record labels (fun i => (fields i).rename ρ)
  | .project e label => .project (e.rename ρ) label

/-- Enter one binder in a simultaneous substitution. -/
def Expr.liftSubst (σ : Nat → Expr) : Nat → Expr
  | 0 => .bvar 0
  | index + 1 => (σ index).rename Nat.succ

def Expr.subst (σ : Nat → Expr) : Expr → Expr
  | .int n => .int n
  | .bool b => .bool b
  | .binary left op right => .binary (left.subst σ) op (right.subst σ)
  | .cond test yes no => .cond (test.subst σ) (yes.subst σ) (no.subst σ)
  | .assign lhs rhs => .assign (lhs.subst σ) (rhs.subst σ)
  | .deref e => .deref (e.subst σ)
  | .ref e => .ref (e.subst σ)
  | .loc address => .loc address
  | .skip => .skip
  | .seq left right => .seq (left.subst σ) (right.subst σ)
  | .loop test body => .loop (test.subst σ) (body.subst σ)
  | .bvar index => σ index
  | .fvar name => .fvar name
  | .lam domain body => .lam domain (body.subst (liftSubst σ))
  | .app fn arg => .app (fn.subst σ) (arg.subst σ)
  | .letE type value body => .letE type (value.subst σ) (body.subst (liftSubst σ))
  | .letRecFun domain codomain functionBody body =>
      .letRecFun domain codomain (functionBody.subst (liftSubst (liftSubst σ)))
        (body.subst (liftSubst σ))
  | .pair left right => .pair (left.subst σ) (right.subst σ)
  | .fst e => .fst (e.subst σ)
  | .snd e => .snd (e.subst σ)
  | .inl e T => .inl (e.subst σ) T
  | .inr e T => .inr (e.subst σ) T
  | .matchSum e A left B right =>
      .matchSum (e.subst σ) A (left.subst (liftSubst σ)) B (right.subst (liftSubst σ))
  | .record labels fields => .record labels (fun i => (fields i).subst σ)
  | .project e label => .project (e.subst σ) label

/-- Discharge the nearest binder without capturing indices in the argument. -/
def Expr.beta (body argument : Expr) : Expr :=
  body.subst (fun
    | 0 => argument
    | index + 1 => .bvar index)

def swapFirstTwo : Nat → Nat
  | 0 => 1
  | 1 => 0
  | index + 2 => index + 2

/-- Unfold a recursive function as in (letrecfun). Under the new lambda and
inner let, the recursive name and the outer parameter trade indices. -/
def Expr.recClosure (domain codomain : Ty) (functionBody : Expr) : Expr :=
  .lam domain (.letRecFun domain codomain
    (functionBody.rename (DeBruijn.liftN 2 Nat.succ))
    (functionBody.rename swapFirstTwo))

end Silmaril.Courses.Cambridge.L3
