module

public import Silmaril.Courses.Cambridge.L3.Store
public import Mathlib.Logic.Function.Basic

/-! # Cambridge L3 evaluation contexts

Sewell (12 February 2026), §5.4, p. 77. Each context has one immediate hole.
Repeated use of the evaluation rule places a computation arbitrarily deep.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3

inductive EvalContext where
  | binaryLeft (op : Op) (right : Expr)
  | binaryRight (left : Value) (op : Op)
  | cond (yes no : Expr)
  | seq (right : Expr)
  | appLeft (arg : Expr)
  | appRight (fn : Value)
  | letE (type : Ty) (body : Expr)
  | pairLeft (right : Expr)
  | pairRight (left : Value)
  | fst
  | snd
  | inl (type : Ty)
  | inr (type : Ty)
  | matchSum (leftType : Ty) (left : Expr) (rightType : Ty) (right : Expr)
  | recordField {labels : RecordLabels} (fields : labels.Index → Expr)
      (i : labels.Index) (earlier : ∀ j, j < i → IsValue (fields j))
  | project (label : Label)
  | assignLeft (rhs : Expr)
  | assignRight (lhs : Value)
  | deref
  | ref

def EvalContext.plug (context : EvalContext) (hole : Expr) : Expr :=
  match context with
  | .binaryLeft op right => .binary hole op right
  | .binaryRight left op => .binary left.val op hole
  | .cond yes no => .cond hole yes no
  | .seq right => .seq hole right
  | .appLeft arg => .app hole arg
  | .appRight fn => .app fn.val hole
  | .letE type body => .letE type hole body
  | .pairLeft right => .pair hole right
  | .pairRight left => .pair left.val hole
  | .fst => .fst hole
  | .snd => .snd hole
  | .inl type => .inl hole type
  | .inr type => .inr hole type
  | .matchSum A left B right => .matchSum hole A left B right
  | .recordField (labels := labels) fields i _ => .record labels (Function.update fields i hole)
  | .project label => .project hole label
  | .assignLeft rhs => .assign hole rhs
  | .assignRight lhs => .assign lhs.val hole
  | .deref => .deref hole
  | .ref => .ref hole

def EvalContext.plugConfig (context : EvalContext) (c : Config) : Config :=
  ⟨context.plug c.expr, c.store⟩

/-- The two presentations differ only in which values may occupy the left
operand when the assignment's right operand is evaluated. -/
def EvalContext.Allows (assignmentLhs : Value → Prop) : EvalContext → Prop
  | .assignRight lhs => assignmentLhs lhs
  | _ => True

def Value.IsLocation (value : Value) : Prop :=
  ∃ address : Loc, value.val = .loc address

/-- The computation rules listed after (eval) on p. 77. The right-injection
case uses (match3) from the collected rules in §5.5. -/
inductive Compute : Config → Config → Prop where
  | add (left right : Int) (s : Store) :
      Compute ⟨.binary (.int left) .add (.int right), s⟩ ⟨.int (left + right), s⟩
  | ge (left right : Int) (s : Store) :
      Compute ⟨.binary (.int left) .ge (.int right), s⟩ ⟨.bool (left ≥ right), s⟩
  | seqSkip {e : Expr} {s : Store} :
      Compute ⟨.seq .skip e, s⟩ ⟨e, s⟩
  | ifTrue {yes no : Expr} {s : Store} :
      Compute ⟨.cond (.bool true) yes no, s⟩ ⟨yes, s⟩
  | ifFalse {yes no : Expr} {s : Store} :
      Compute ⟨.cond (.bool false) yes no, s⟩ ⟨no, s⟩
  | while {test body : Expr} {s : Store} :
      Compute ⟨.loop test body, s⟩ ⟨.cond test (.seq body (.loop test body)) .skip, s⟩
  | appFun {domain : Ty} {body arg : Expr} {s : Store} :
      IsValue arg → Compute ⟨.app (.lam domain body) arg, s⟩ ⟨body.beta arg, s⟩
  | letValue {T : Ty} {value body : Expr} {s : Store} :
      IsValue value → Compute ⟨.letE T value body, s⟩ ⟨body.beta value, s⟩
  | letRecFun {domain codomain : Ty} {functionBody body : Expr} {s : Store} :
      Compute ⟨.letRecFun domain codomain functionBody body, s⟩
        ⟨body.beta (Expr.recClosure domain codomain functionBody), s⟩
  | fstValue {left right : Expr} {s : Store} :
      IsValue left → IsValue right → Compute ⟨.fst (.pair left right), s⟩ ⟨left, s⟩
  | sndValue {left right : Expr} {s : Store} :
      IsValue left → IsValue right → Compute ⟨.snd (.pair left right), s⟩ ⟨right, s⟩
  | matchLeft {payload left right : Expr} {A B T : Ty} {s : Store} :
      IsValue payload → Compute ⟨.matchSum (.inl payload T) A left B right, s⟩
        ⟨left.beta payload, s⟩
  | matchRight {payload left right : Expr} {A B T : Ty} {s : Store} :
      IsValue payload → Compute ⟨.matchSum (.inr payload T) A left B right, s⟩
        ⟨right.beta payload, s⟩
  | projectValue {labels : RecordLabels} {fields : labels.Index → Expr} {s : Store}
      (i : labels.Index) (ready : ∀ j, IsValue (fields j)) :
      Compute ⟨.project (.record labels fields) (labels.label i), s⟩ ⟨fields i, s⟩
  | refValue {s : Store} (value : Value) {loc : Loc} (fresh : loc ∉ s) :
      Compute ⟨.ref value.val, s⟩ ⟨.loc loc, s.insert loc value⟩
  | derefValue {s : Store} {loc : Loc} {value : Value} (present : s.lookup loc = some value) :
      Compute ⟨.deref (.loc loc), s⟩ ⟨value.val, s⟩
  | assignValue {s : Store} {loc : Loc} (value : Value) (present : loc ∈ s) :
      Compute ⟨.assign (.loc loc) value.val, s⟩ ⟨.skip, s.insert loc value⟩

inductive ContextStepWith (assignmentLhs : Value → Prop) : Config → Config → Prop where
  | compute {before after : Config} : Compute before after → ContextStepWith assignmentLhs before after
  | eval {before after : Config} (context : EvalContext) (allowed : context.Allows assignmentLhs) :
      ContextStepWith assignmentLhs before after →
      ContextStepWith assignmentLhs (context.plugConfig before) (context.plugConfig after)

/-- The printed context rules in §5.4, including the assignment frame `v := □`. -/
abbrev ContextStep := ContextStepWith (fun _ => True)

/-- The context rules using the location premise from (assign2) in §5.5. -/
abbrev LocationContextStep := ContextStepWith Value.IsLocation

end Silmaril.Courses.Cambridge.L3
