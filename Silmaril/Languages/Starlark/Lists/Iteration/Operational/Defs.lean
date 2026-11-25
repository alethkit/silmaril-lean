module

public import Silmaril.Languages.Starlark.Lists.Iteration.Defs
public import Silmaril.Languages.Starlark.Lists.Operational.Defs

public section

namespace Silmaril.Languages.Starlark.Lists.Iteration

/-- Materialization follows the order in which the cursor yields elements. -/
inductive CursorCollects : Cursor → List Value → Prop where
  | done {cursor : Cursor} : cursor.advance = none → CursorCollects cursor []
  | next {cursor rest : Cursor} {value : Value} {tail : List Value} :
      cursor.advance = some (value, rest) → CursorCollects rest tail →
      CursorCollects cursor (value :: tail)

inductive WritesBindings : State → List (Binding × Value) → State → Prop where
  | done (s : State) : WritesBindings s [] s
  | next {s final : State} {binding : Binding} {value : Value} {rest : List (Binding × Value)} :
      WritesBindings (s.write binding value) rest final →
      WritesBindings s ((binding, value) :: rest) final

/-- Unpack and validate an item before any writes to a flat target. -/
inductive BindsTarget (s : State) (value : Value) : LoopTarget → Outcome Unit → Prop where
  | name (binding : Binding) : BindsTarget s value (.name binding) (.ok () (s.write binding value))
  | unpack {bindings : List Binding} {values : List Value} {guard : Option Address}
      {cursor : Cursor} {t final : State} :
      acquireIterator value s = .ok (guard, cursor) t → cursor.remaining = bindings.length →
      CursorCollects cursor values → WritesBindings t (bindings.zip values) final →
      BindsTarget s value (.unpack bindings) (.ok () final)
  | arity {bindings : List Binding} {guard : Option Address} {cursor : Cursor} {t : State} :
      acquireIterator value s = .ok (guard, cursor) t → cursor.remaining ≠ bindings.length →
      BindsTarget s value (.unpack bindings) (.error (.unpackArity bindings.length cursor.remaining) t)
  | nonIterable (bindings : List Binding) {t : State} :
      acquireIterator value s = .error .notIterable t →
      BindsTarget s value (.unpack bindings) (.error (.unpackTarget value) t)
  | readError (bindings : List Binding) {error : Error} {t : State} :
      acquireIterator value s = .error error t → error ≠ .notIterable →
      BindsTarget s value (.unpack bindings) (.error error t)

/-- Step rules shared by the suite and checked-body loop judgments. -/
inductive CursorRuns (body : State → Outcome Flow → Prop) (target : LoopTarget) :
    Cursor → State → Outcome Flow → Prop where
  | done {cursor : Cursor} {s : State} :
      cursor.advance = none → CursorRuns body target cursor s (.ok .next s)
  | advance {cursor rest : Cursor} {s u t : State} {value : Value} {signal : Flow} {out : Outcome Flow} :
      cursor.advance = some (value, rest) → BindsTarget s value target (.ok () u) → body u (.ok signal t) →
      (signal = .next ∨ signal = .continueLoop) → CursorRuns body target rest t out →
      CursorRuns body target cursor s out
  | breakLoop {cursor rest : Cursor} {s u t : State} {value : Value} :
      cursor.advance = some (value, rest) → BindsTarget s value target (.ok () u) → body u (.ok .breakLoop t) →
      CursorRuns body target cursor s (.ok .next t)
  | returned {cursor rest : Cursor} {s u t : State} {value result : Value} :
      cursor.advance = some (value, rest) → BindsTarget s value target (.ok () u) →
      body u (.ok (.returned result) t) →
      CursorRuns body target cursor s (.ok (.returned result) t)
  | failed {cursor rest : Cursor} {s u t : State} {value : Value} {error : Error} :
      cursor.advance = some (value, rest) → BindsTarget s value target (.ok () u) → body u (.error error t) →
      CursorRuns body target cursor s (.error error t)
  | bindingError {cursor rest : Cursor} {s t : State} {value : Value} {error : Error} :
      cursor.advance = some (value, rest) → BindsTarget s value target (.error error t) →
      CursorRuns body target cursor s (.error error t)

/-- Suite and cursor judgments share one induction principle. -/
inductive Work where
  | suite {depth : Nat} (code : Suite depth)
  | cursor {depth : Nat} (target : LoopTarget) (body : Suite depth) (remaining : Cursor)

abbrev Work.items {depth : Nat} (target : Binding) (body : Suite depth) (remaining : List Value) : Work :=
  .cursor target body (.items remaining)

/-- Collection loops own a guard while the body runs. On exit, every loop
restores the iterator stack from before it entered. -/
inductive Runs : State → Work → Outcome Flow → Prop where
  | atomic {depth : Nat} {s : State} {stmt : Stmt} {out : Outcome Unit} :
      Eval s stmt out → Runs s (.suite (.atomic (depth := depth) stmt))
        (Outcome.resume out fun () => pure .next)
  | seq {depth : Nat} {s t : State} {first rest : Suite depth} {out : Outcome Flow} :
      Runs s (.suite first) (.ok .next t) → Runs t (.suite rest) out →
      Runs s (.suite (.seq first rest)) out
  | seqStop {depth : Nat} {s t : State} {first rest : Suite depth} {signal : Flow} :
      Runs s (.suite first) (.ok signal t) → signal ≠ .next →
      Runs s (.suite (.seq first rest)) (.ok signal t)
  | seqError {depth : Nat} {s t : State} {first rest : Suite depth} {error : Error} :
      Runs s (.suite first) (.error error t) →
      Runs s (.suite (.seq first rest)) (.error error t)
  | branch {depth : Nat} {s t : State} {test : Expr} {yes no : Suite depth}
      {value : Outcome Value} {flag : Bool} {out : Outcome Flow} :
      Eval s test value → Outcome.resume value truth = .ok flag t →
      Runs t (.suite (if flag then yes else no)) out →
      Runs s (.suite (.branch test yes no)) out
  | branchError {depth : Nat} {s t : State} {test : Expr} {yes no : Suite depth}
      {value : Outcome Value} {error : Error} :
      Eval s test value → Outcome.resume value truth = .error error t →
      Runs s (.suite (.branch test yes no)) (.error error t)
  | forIn {depth : Nat} {s t : State} {target : LoopTarget} {iterable : Expr}
      {body : Suite (depth + 1)} {value : Outcome Value} {guard : Option Address}
      {cursor : Cursor} {out : Outcome Flow} :
      Eval s iterable value → Outcome.resume value acquireIterator = .ok (guard, cursor) t →
      Runs (enterIterator t guard) (.cursor target body cursor) out →
      Runs s (.suite (.forIn target iterable body)) (restoreIterators t.iterators out)
  | forError {depth : Nat} {s t : State} {target : LoopTarget} {iterable : Expr}
      {body : Suite (depth + 1)} {value : Outcome Value} {error : Error} :
      Eval s iterable value → Outcome.resume value acquireIterator = .error error t →
      Runs s (.suite (.forIn target iterable body)) (.error error t)
  | breakLoop {depth : Nat} {s : State} :
      Runs s (.suite (.breakLoop (depth := depth))) (.ok .breakLoop s)
  | continueLoop {depth : Nat} {s : State} :
      Runs s (.suite (.continueLoop (depth := depth))) (.ok .continueLoop s)
  | ret {depth : Nat} {s : State} {value : Expr} {out : Outcome Value} :
      Eval s value out → Runs s (.suite (.ret (depth := depth) value))
        (Outcome.resume out fun result => pure (.returned result))
  | cursor {depth : Nat} {s : State} {target : LoopTarget} {body : Suite depth}
      {remaining : Cursor} {out : Outcome Flow} {bodyRuns : State → Outcome Flow → Prop} :
      (∀ state result, bodyRuns state result → Runs state (.suite body) result) →
      CursorRuns bodyRuns target remaining s out → Runs s (.cursor target body remaining) out

end Silmaril.Languages.Starlark.Lists.Iteration
