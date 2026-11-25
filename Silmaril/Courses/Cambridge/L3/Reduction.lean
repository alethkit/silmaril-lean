module

public import Silmaril.Courses.Cambridge.L3.Store
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Relation

/-! # Cambridge L3 small-step reduction

The direct rules are from §5.5, pp. 78–80. Evaluation is strict and
left to right. Allocation can choose any location outside the store's domain.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3

inductive Step : Config → Config → Prop where
  | add (left right : Int) (s : Store) :
      Step ⟨.binary (.int left) .add (.int right), s⟩ ⟨.int (left + right), s⟩
  | ge (left right : Int) (s : Store) :
      Step ⟨.binary (.int left) .ge (.int right), s⟩ ⟨.bool (left ≥ right), s⟩
  | binaryLeft {left left' right : Expr} {op : Op} {s s' : Store} :
      Step ⟨left, s⟩ ⟨left', s'⟩ →
      Step ⟨.binary left op right, s⟩ ⟨.binary left' op right, s'⟩
  | binaryRight {left right right' : Expr} {op : Op} {s s' : Store} :
      IsValue left → Step ⟨right, s⟩ ⟨right', s'⟩ →
      Step ⟨.binary left op right, s⟩ ⟨.binary left op right', s'⟩
  | seqSkip {e : Expr} {s : Store} :
      Step ⟨.seq .skip e, s⟩ ⟨e, s⟩
  | seqStep {left left' right : Expr} {s s' : Store} :
      Step ⟨left, s⟩ ⟨left', s'⟩ →
      Step ⟨.seq left right, s⟩ ⟨.seq left' right, s'⟩
  | ifTrue {yes no : Expr} {s : Store} :
      Step ⟨.cond (.bool true) yes no, s⟩ ⟨yes, s⟩
  | ifFalse {yes no : Expr} {s : Store} :
      Step ⟨.cond (.bool false) yes no, s⟩ ⟨no, s⟩
  | ifStep {test test' yes no : Expr} {s s' : Store} :
      Step ⟨test, s⟩ ⟨test', s'⟩ →
      Step ⟨.cond test yes no, s⟩ ⟨.cond test' yes no, s'⟩
  | while {test body : Expr} {s : Store} :
      Step ⟨.loop test body, s⟩ ⟨.cond test (.seq body (.loop test body)) .skip, s⟩
  | appLeft {fn fn' arg : Expr} {s s' : Store} :
      Step ⟨fn, s⟩ ⟨fn', s'⟩ → Step ⟨.app fn arg, s⟩ ⟨.app fn' arg, s'⟩
  | appRight {fn arg arg' : Expr} {s s' : Store} :
      IsValue fn → Step ⟨arg, s⟩ ⟨arg', s'⟩ →
      Step ⟨.app fn arg, s⟩ ⟨.app fn arg', s'⟩
  | appFun {domain : Ty} {body arg : Expr} {s : Store} :
      IsValue arg → Step ⟨.app (.lam domain body) arg, s⟩ ⟨body.beta arg, s⟩
  | letStep {T : Ty} {value value' body : Expr} {s s' : Store} :
      Step ⟨value, s⟩ ⟨value', s'⟩ →
      Step ⟨.letE T value body, s⟩ ⟨.letE T value' body, s'⟩
  | letValue {T : Ty} {value body : Expr} {s : Store} :
      IsValue value → Step ⟨.letE T value body, s⟩ ⟨body.beta value, s⟩
  | letRecFun {domain codomain : Ty} {functionBody body : Expr} {s : Store} :
      Step ⟨.letRecFun domain codomain functionBody body, s⟩
        ⟨body.beta (Expr.recClosure domain codomain functionBody), s⟩
  | pairLeft {left left' right : Expr} {s s' : Store} :
      Step ⟨left, s⟩ ⟨left', s'⟩ → Step ⟨.pair left right, s⟩ ⟨.pair left' right, s'⟩
  | pairRight {left right right' : Expr} {s s' : Store} :
      IsValue left → Step ⟨right, s⟩ ⟨right', s'⟩ →
      Step ⟨.pair left right, s⟩ ⟨.pair left right', s'⟩
  | fstValue {left right : Expr} {s : Store} :
      IsValue left → IsValue right → Step ⟨.fst (.pair left right), s⟩ ⟨left, s⟩
  | sndValue {left right : Expr} {s : Store} :
      IsValue left → IsValue right → Step ⟨.snd (.pair left right), s⟩ ⟨right, s⟩
  | fstStep {e e' : Expr} {s s' : Store} :
      Step ⟨e, s⟩ ⟨e', s'⟩ → Step ⟨.fst e, s⟩ ⟨.fst e', s'⟩
  | sndStep {e e' : Expr} {s s' : Store} :
      Step ⟨e, s⟩ ⟨e', s'⟩ → Step ⟨.snd e, s⟩ ⟨.snd e', s'⟩
  | inl {e e' : Expr} {T : Ty} {s s' : Store} :
      Step ⟨e, s⟩ ⟨e', s'⟩ → Step ⟨.inl e T, s⟩ ⟨.inl e' T, s'⟩
  | inr {e e' : Expr} {T : Ty} {s s' : Store} :
      Step ⟨e, s⟩ ⟨e', s'⟩ → Step ⟨.inr e T, s⟩ ⟨.inr e' T, s'⟩
  | matchStep {e e' left right : Expr} {A B : Ty} {s s' : Store} :
      Step ⟨e, s⟩ ⟨e', s'⟩ → Step ⟨.matchSum e A left B right, s⟩
        ⟨.matchSum e' A left B right, s'⟩
  | matchLeft {payload left right : Expr} {A B T : Ty} {s : Store} :
      IsValue payload → Step ⟨.matchSum (.inl payload T) A left B right, s⟩
        ⟨left.beta payload, s⟩
  | matchRight {payload left right : Expr} {A B T : Ty} {s : Store} :
      IsValue payload → Step ⟨.matchSum (.inr payload T) A left B right, s⟩
        ⟨right.beta payload, s⟩
  | recordStep {labels : RecordLabels} {fields : labels.Index → Expr} {e' : Expr}
      {s s' : Store} (i : labels.Index) (earlier : ∀ j, j < i → IsValue (fields j)) :
      Step ⟨fields i, s⟩ ⟨e', s'⟩ →
      Step ⟨.record labels fields, s⟩ ⟨.record labels (Function.update fields i e'), s'⟩
  | projectValue {labels : RecordLabels} {fields : labels.Index → Expr} {s : Store}
      (i : labels.Index) (ready : ∀ j, IsValue (fields j)) :
      Step ⟨.project (.record labels fields) (labels.label i), s⟩ ⟨fields i, s⟩
  | projectStep {e e' : Expr} {label : Label} {s s' : Store} :
      Step ⟨e, s⟩ ⟨e', s'⟩ → Step ⟨.project e label, s⟩ ⟨.project e' label, s'⟩
  | refValue {s : Store} (value : Value) {loc : Loc} (fresh : loc ∉ s) :
      Step ⟨.ref value.val, s⟩ ⟨.loc loc, s.insert loc value⟩
  | refStep {e e' : Expr} {s s' : Store} :
      Step ⟨e, s⟩ ⟨e', s'⟩ → Step ⟨.ref e, s⟩ ⟨.ref e', s'⟩
  | derefValue {s : Store} {loc : Loc} {value : Value} (present : s.lookup loc = some value) :
      Step ⟨.deref (.loc loc), s⟩ ⟨value.val, s⟩
  | derefStep {e e' : Expr} {s s' : Store} :
      Step ⟨e, s⟩ ⟨e', s'⟩ → Step ⟨.deref e, s⟩ ⟨.deref e', s'⟩
  | assignValue {s : Store} {loc : Loc} (value : Value) (present : loc ∈ s) :
      Step ⟨.assign (.loc loc) value.val, s⟩ ⟨.skip, s.insert loc value⟩
  | assignRight {e e' : Expr} {loc : Loc} {s s' : Store} :
      Step ⟨e, s⟩ ⟨e', s'⟩ → Step ⟨.assign (.loc loc) e, s⟩ ⟨.assign (.loc loc) e', s'⟩
  | assignLeft {lhs lhs' rhs : Expr} {s s' : Store} :
      Step ⟨lhs, s⟩ ⟨lhs', s'⟩ → Step ⟨.assign lhs rhs, s⟩ ⟨.assign lhs' rhs, s'⟩

abbrev Steps : Config → Config → Prop := Relation.ReflTransGen Step

def Stuck (c : Config) : Prop :=
  ¬ IsValue c.expr ∧ ∀ next, ¬ Step c next

end Silmaril.Courses.Cambridge.L3
