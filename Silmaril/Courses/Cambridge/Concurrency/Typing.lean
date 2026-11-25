module

public import Silmaril.Courses.Cambridge.Concurrency.Syntax
public import Silmaril.Courses.Cambridge.L1.Typing

/-! # Typing the concurrent extension of L1

Page 90 adds the type `proc` and the (thread) and (parallel) rules. A thread
is an expression of type `unit` viewed as a process by a typing rule.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency

abbrev TypeEnv := L1.TypeEnv

inductive Ty where
  | int
  | bool
  | unit
  | proc
  deriving DecidableEq, Repr

inductive HasType (Γ : TypeEnv) : Expr → Ty → Prop where
  | int (n : Int) : HasType Γ (.int n) .int
  | bool (b : Bool) : HasType Γ (.bool b) .bool
  | add {left right : Expr} (hl : HasType Γ left .int) (hr : HasType Γ right .int) :
      HasType Γ (.binary left .add right) .int
  | ge {left right : Expr} (hl : HasType Γ left .int) (hr : HasType Γ right .int) :
      HasType Γ (.binary left .ge right) .bool
  | cond {test yes no : Expr} {T : Ty}
      (hc : HasType Γ test .bool) (hy : HasType Γ yes T) (hn : HasType Γ no T) :
      HasType Γ (.cond test yes no) T
  | assign {loc : Loc} {e : Expr} (present : loc ∈ Γ) (he : HasType Γ e .int) :
      HasType Γ (.assign loc e) .unit
  | deref {loc : Loc} (present : loc ∈ Γ) : HasType Γ (.deref loc) .int
  | skip : HasType Γ .skip .unit
  | seq {left right : Expr} {T : Ty}
      (hl : HasType Γ left .unit) (hr : HasType Γ right T) :
      HasType Γ (.seq left right) T
  | loop {test body : Expr}
      (ht : HasType Γ test .bool) (hb : HasType Γ body .unit) :
      HasType Γ (.loop test body) .unit
  | thread {e : Expr} (typing : HasType Γ e .unit) : HasType Γ e .proc
  | parallel {left right : Expr} (hl : HasType Γ left .proc) (hr : HasType Γ right .proc) :
      HasType Γ (.parallel left right) .proc

def Ty.ofL1 : L1.Ty → Ty
  | .int => .int
  | .bool => .bool
  | .unit => .unit

theorem HasType.ofL1 {Γ : TypeEnv} {e : L1.Expr} {T : L1.Ty} (typed : L1.HasType Γ e T) :
    HasType Γ (Expr.ofL1 e) (Ty.ofL1 T) := by
  induction typed with
  | int n => exact .int n
  | bool b => exact .bool b
  | add _ _ ihl ihr => exact .add ihl ihr
  | ge _ _ ihl ihr => exact .ge ihl ihr
  | cond _ _ _ ihc ihy ihn => exact .cond ihc ihy ihn
  | assign present _ ih => exact .assign present ih
  | deref present => exact .deref present
  | skip => exact .skip
  | seq _ _ ihl ihr => exact .seq ihl ihr
  | loop _ _ iht ihb => exact .loop iht ihb

end Silmaril.Courses.Cambridge.Concurrency
