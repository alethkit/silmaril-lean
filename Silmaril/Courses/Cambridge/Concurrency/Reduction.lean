module

public import Silmaril.Courses.Cambridge.Concurrency.Syntax
public import Silmaril.Courses.Cambridge.L1.Reduction

/-! # Global interleaving over one shared store

The two parallel rules on p. 90 extend the L1 rules from p. 29. A parallel
step takes one step on either side and passes the resulting store to both
threads. Writes of integer values and reads each take one step.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency

abbrev Store := L1.Store

structure Config where
  expr : Expr
  store : Store
  deriving DecidableEq

inductive Step : Config → Config → Prop where
  | add (left right : Int) (s : Store) :
      Step ⟨.binary (.int left) .add (.int right), s⟩ ⟨.int (left + right), s⟩
  | ge (left right : Int) (s : Store) :
      Step ⟨.binary (.int left) .ge (.int right), s⟩ ⟨.bool (left ≥ right), s⟩
  | binaryLeft {left left' right : Expr} {op : Op} {s s' : Store}
      (inner : Step ⟨left, s⟩ ⟨left', s'⟩) :
      Step ⟨.binary left op right, s⟩ ⟨.binary left' op right, s'⟩
  | binaryRight {left right right' : Expr} {op : Op} {s s' : Store}
      (value : IsValue left) (inner : Step ⟨right, s⟩ ⟨right', s'⟩) :
      Step ⟨.binary left op right, s⟩ ⟨.binary left op right', s'⟩
  | deref {loc : Loc} {s : Store} {n : Int} (present : L1.Store.lookup s loc = some n) :
      Step ⟨.deref loc, s⟩ ⟨.int n, s⟩
  | assignValue {loc : Loc} {s : Store} {n : Int} (present : loc ∈ s) :
      Step ⟨.assign loc (.int n), s⟩ ⟨.skip, s.insert loc n⟩
  | assignStep {loc : Loc} {e e' : Expr} {s s' : Store}
      (inner : Step ⟨e, s⟩ ⟨e', s'⟩) :
      Step ⟨.assign loc e, s⟩ ⟨.assign loc e', s'⟩
  | seqSkip {e : Expr} {s : Store} :
      Step ⟨.seq .skip e, s⟩ ⟨e, s⟩
  | seqStep {left left' right : Expr} {s s' : Store}
      (inner : Step ⟨left, s⟩ ⟨left', s'⟩) :
      Step ⟨.seq left right, s⟩ ⟨.seq left' right, s'⟩
  | ifTrue {yes no : Expr} {s : Store} :
      Step ⟨.cond (.bool true) yes no, s⟩ ⟨yes, s⟩
  | ifFalse {yes no : Expr} {s : Store} :
      Step ⟨.cond (.bool false) yes no, s⟩ ⟨no, s⟩
  | ifStep {test test' yes no : Expr} {s s' : Store}
      (inner : Step ⟨test, s⟩ ⟨test', s'⟩) :
      Step ⟨.cond test yes no, s⟩ ⟨.cond test' yes no, s'⟩
  | while {test body : Expr} {s : Store} :
      Step ⟨.loop test body, s⟩
        ⟨.cond test (.seq body (.loop test body)) .skip, s⟩
  | parallelLeft {left left' right : Expr} {s s' : Store}
      (inner : Step ⟨left, s⟩ ⟨left', s'⟩) :
      Step ⟨.parallel left right, s⟩ ⟨.parallel left' right, s'⟩
  | parallelRight {left right right' : Expr} {s s' : Store}
      (inner : Step ⟨right, s⟩ ⟨right', s'⟩) :
      Step ⟨.parallel left right, s⟩ ⟨.parallel left right', s'⟩

abbrev Steps : Config → Config → Prop := Relation.ReflTransGen Step

def Terminal (c : Config) : Prop := ∀ next, ¬ Step c next

def Config.ofL1 (c : L1.Config) : Config := ⟨Expr.ofL1 c.expr, c.store⟩

private theorem IsValue.ofL1 {e : L1.Expr} (value : L1.IsValue e) : IsValue (Expr.ofL1 e) := by
  cases value with
  | int n => exact .int n
  | bool b => exact .bool b
  | skip => exact .skip

theorem Step.ofL1 {before after : L1.Config} (step : L1.Step before after) :
    Step (Config.ofL1 before) (Config.ofL1 after) := by
  induction step with
  | add l r s => exact .add l r s
  | ge l r s => exact .ge l r s
  | binaryLeft _ ih => exact .binaryLeft ih
  | binaryRight value _ ih => exact .binaryRight (IsValue.ofL1 value) ih
  | deref present => exact .deref present
  | assignValue present => exact .assignValue present
  | assignStep _ ih => exact .assignStep ih
  | seqSkip => exact .seqSkip
  | seqStep _ ih => exact .seqStep ih
  | ifTrue => exact .ifTrue
  | ifFalse => exact .ifFalse
  | ifStep _ ih => exact .ifStep ih
  | «while» => exact .while

theorem ProcessDone.terminal {e : Expr} {s : Store} (finished : ProcessDone e) :
    Terminal ⟨e, s⟩ := by
  intro next step
  induction finished generalizing next with
  | skip => cases step
  | parallel _ _ ihl ihr =>
      cases step with
      | parallelLeft inner => exact ihl _ inner
      | parallelRight inner => exact ihr _ inner

end Silmaril.Courses.Cambridge.Concurrency
