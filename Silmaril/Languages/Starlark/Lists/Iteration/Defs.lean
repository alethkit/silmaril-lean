module

public import Silmaril.Languages.Starlark.Lists.Denotation.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists.Iteration

/-- Resolved function suites. The index counts lexically enclosing loops. -/
inductive Suite : Nat → Type where
  | atomic {depth : Nat} (stmt : Stmt) : Suite depth
  | seq {depth : Nat} (first rest : Suite depth) : Suite depth
  | branch {depth : Nat} (test : Expr) (yes no : Suite depth) : Suite depth
  | forIn {depth : Nat} (target : Binding) (iterable : Expr)
      (body : Suite (depth + 1)) : Suite depth
  | breakLoop {depth : Nat} : Suite (depth + 1)
  | continueLoop {depth : Nat} : Suite (depth + 1)
  | ret {depth : Nat} (value : Expr) : Suite depth

/-- The original list-only constructor spelling remains available to clients. -/
abbrev Suite.forList {depth : Nat} (target : Binding) (iterable : Expr)
    (body : Suite (depth + 1)) : Suite depth :=
  .forIn target iterable body

inductive Flow where
  | next | breakLoop | continueLoop | returned (value : Value)
  deriving DecidableEq, Repr

def finishState {α : Type} : Outcome α → State
  | .ok _ state | .error _ state => state

def restoreIterators {α : Type} (stack : List Address) : Outcome α → Outcome α
  | .ok value state => .ok value { state with iterators := stack }
  | .error error state => .error error { state with iterators := stack }

def pushIterator (state : State) (address : Address) : State :=
  { state with iterators := address :: state.iterators }

def truth : Value → Meaning Bool
  | .scalar value => pure value.truth
  | .function _ | .builtin _ => pure true
  | .string text => pure (!text.isEmpty)
  | .range span => pure (span.length != 0)
  | .list address => (fun elements => !elements.isEmpty) <$> listElements address
  | .tuple address => (fun elements => !elements.isEmpty) <$> tupleElements address
  | .dict address => (fun entries => !entries.isEmpty) <$> dictEntries address

def iterationSource : Value → Meaning (Address × List Value)
  | .scalar _ | .function _ | .builtin _ | .string _ | .range _ => throw .notIterable
  | .list address => (fun elements => (address, elements)) <$> listElements address
  | .tuple address => (fun elements => (address, elements)) <$> tupleElements address
  | .dict address => (fun entries => (address, entries.map Entry.key)) <$> dictEntries address

/-- An acquired collection snapshot or an exact arithmetic range cursor. -/
inductive Cursor where
  | items (remaining : List Value)
  | range (current step : Int) (remaining : Nat)

def Cursor.ofRange (span : RangeValue) : Cursor :=
  .range span.start span.step span.length

def Cursor.remaining : Cursor → Nat
  | .items values => values.length
  | .range _ _ count => count

def Cursor.advance : Cursor → Option (Value × Cursor)
  | .items [] | .range _ _ 0 => none
  | .items (value :: rest) => some (value, .items rest)
  | .range current step (count + 1) =>
    some (.scalar (.int current), .range (current + step) step count)

theorem Cursor.advance_decreases {cursor next : Cursor} {value : Value}
    (step : cursor.advance = some (value, next)) : next.remaining < cursor.remaining := by
  cases cursor with
  | items values => cases values <;> simp [Cursor.advance] at step <;> simp [← step.2, Cursor.remaining]
  | range current stride count => cases count <;> simp [Cursor.advance] at step <;> simp [← step.2, Cursor.remaining]

/-- Collect the cursor in yield order for operations that materialize an iterable. -/
def Cursor.collect (cursor : Cursor) : List Value := go cursor []
where
  go (cursor : Cursor) (reversed : List Value) : List Value :=
    match _step : cursor.advance with
    | none => reversed.reverse
    | some (value, rest) => go rest (value :: reversed)
  termination_by cursor.remaining
  decreasing_by exact Cursor.advance_decreases _step

/-- Ranges need no heap guard. Other iterables keep the existing snapshot and guard. -/
def acquireIterator : Value → Meaning (Option Address × Cursor)
  | .range span => pure (none, .ofRange span)
  | value => (fun (address, items) => (some address, .items items)) <$> iterationSource value

def enterIterator (state : State) : Option Address → State
  | none => state
  | some address => pushIterator state address

/-- Consume one item, advancing only if the body permits another iteration. -/
def denoteCursor (target : Binding) (body : Meaning Flow) (cursor : Cursor) (state : State) : Outcome Flow :=
  match _step : cursor.advance with
  | none => .ok .next state
  | some (value, rest) =>
    match body (state.write target value) with
    | .ok .next next | .ok .continueLoop next => denoteCursor target body rest next
    | .ok .breakLoop next => .ok .next next
    | .ok (.returned result) next => .ok (.returned result) next
    | .error error next => .error error next
termination_by cursor.remaining
decreasing_by all_goals exact Cursor.advance_decreases _step

abbrev denoteItems (target : Binding) (body : Meaning Flow) (items : List Value) : Meaning Flow :=
  denoteCursor target body (.items items)

/-- Acquire an iterator from a completed operand, run its cursor,
and restore the previous guard stack on every exit. -/
def denoteForIn (target : Binding) (body : Meaning Flow) (operand : Outcome Value) : Outcome Flow :=
  Outcome.resume (Outcome.resume operand acquireIterator) fun (guard, cursor) next =>
    restoreIterators next.iterators (denoteCursor target body cursor (enterIterator next guard))

def denoteSuite {depth : Nat} : Suite depth → Meaning Flow
  | .atomic stmt, state => Outcome.resume (denote stmt state) fun () => pure .next
  | .seq first rest, state =>
    Outcome.resume (denoteSuite first state) fun
      | .next => denoteSuite rest
      | signal => pure signal
  | .branch test yes no, state =>
    Outcome.resume (Outcome.resume (denote test state) truth) fun test =>
      if test then denoteSuite yes else denoteSuite no
  | .forIn target iterable body, state =>
    denoteForIn target (denoteSuite body) (denote iterable state)
  | .breakLoop, state => .ok .breakLoop state
  | .continueLoop, state => .ok .continueLoop state
  | .ret value, state => Outcome.resume (denote value state) fun result => pure (.returned result)

end Silmaril.Languages.Starlark.Lists.Iteration
