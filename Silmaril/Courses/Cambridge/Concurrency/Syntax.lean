module

public import Silmaril.Courses.Cambridge.L1.Syntax

/-! # Shared-store concurrency in Cambridge L1

The parallel extension of L1 in Sewell (12 February 2026), chapter 7, p. 90.
Source `sewell2026semantics` in `references.bib`.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency

abbrev Loc := L1.Loc
abbrev Op := L1.Op

inductive Expr where
  | int (value : Int)
  | bool (value : Bool)
  | binary (left : Expr) (op : Op) (right : Expr)
  | cond (test yes no : Expr)
  | assign (loc : Loc) (rhs : Expr)
  | deref (loc : Loc)
  | skip
  | seq (left right : Expr)
  | loop (test body : Expr)
  | parallel (left right : Expr)
  deriving DecidableEq, Repr

/-- Embed a sequential L1 expression into the extended grammar. -/
def Expr.ofL1 : L1.Expr → Expr
  | .int n => .int n
  | .bool b => .bool b
  | .binary left op right => .binary (ofL1 left) op (ofL1 right)
  | .cond test yes no => .cond (ofL1 test) (ofL1 yes) (ofL1 no)
  | .assign loc rhs => .assign loc (ofL1 rhs)
  | .deref loc => .deref loc
  | .skip => .skip
  | .seq left right => .seq (ofL1 left) (ofL1 right)
  | .loop test body => .loop (ofL1 test) (ofL1 body)

inductive IsValue : Expr → Prop where
  | int (n : Int) : IsValue (.int n)
  | bool (b : Bool) : IsValue (.bool b)
  | skip : IsValue .skip

/-- A finished process consists of `skip` leaves. The parallel tree retains
the shape of the program's thread composition. -/
inductive ProcessDone : Expr → Prop where
  | skip : ProcessDone .skip
  | parallel {left right : Expr} :
      ProcessDone left → ProcessDone right → ProcessDone (.parallel left right)

end Silmaril.Courses.Cambridge.Concurrency
