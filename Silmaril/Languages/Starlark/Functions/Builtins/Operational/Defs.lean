module

public import Silmaril.Languages.Starlark.Functions.Builtins.Defs
public import Silmaril.Languages.Starlark.Lists.Iteration.Operational.Defs

public section

namespace Silmaril.Languages.Starlark.Functions.Builtins

open Lists
open Lists.Iteration (Cursor CursorCollects truth)

@[expose] def IsCollection : Lists.Value → Prop
  | .list _ | .tuple _ | .dict _ | .range _ => True
  | _ => False

/-- Obtain the ordered items of a collection. Dictionaries yield keys;
ranges derive their elements by cursor steps. -/
inductive Items (id : Builtin) (state : State) :
    Lists.Value → Outcome (List Lists.Value) → Prop where
  | list (address : Address) : Items id state (.list address) (listElements address state)
  | tuple (address : Address) : Items id state (.tuple address) (tupleElements address state)
  | dict (address : Address) : Items id state (.dict address)
      (Outcome.resume (dictEntries address state) fun entries => pure (entries.map Entry.key))
  | range {span : RangeValue} {values : List Lists.Value} :
      CursorCollects (Cursor.ofRange span) values → Items id state (.range span) (.ok values state)
  | invalid {value : Lists.Value} : ¬ IsCollection value →
      Items id state value (.error (.builtinType id value) state)

/-- Built-in calls on expanded arguments, with independent arity, type and
store premises. Collection allocation reuses the shared heap primitives. -/
inductive Invokes (state : State) : Builtin → Actual → Outcome Lists.Value → Prop where
  | keyword {id : Builtin} {values : List Lists.Value} {name : String}
      {value : Lists.Value} {rest : List (String × Lists.Value)} :
      Invokes state id ⟨values, (name, value) :: rest⟩ (.error (.builtinKeyword id name) state)
  | missing {id : Builtin} : minArity id = 1 →
      Invokes state id ⟨[], []⟩ (.error (arityError id 0) state)
  | extra {id : Builtin} {first second : Lists.Value} {rest : List Lists.Value} :
      id ≠ .range →
      Invokes state id ⟨first :: second :: rest, []⟩
        (.error (arityError id (first :: second :: rest).length) state)
  | rangeExtra {a b c d : Lists.Value} {rest : List Lists.Value} :
      Invokes state .range ⟨a :: b :: c :: d :: rest, []⟩
        (.error (arityError .range (a :: b :: c :: d :: rest).length) state)
  | rangeOne {stop : Lists.Value} :
      Invokes state .range ⟨[stop], []⟩
        (fromExcept (checkedRange (.scalar (.int 0)) stop (.scalar (.int 1))) state)
  | rangeTwo {start stop : Lists.Value} :
      Invokes state .range ⟨[start, stop], []⟩
        (fromExcept (checkedRange start stop (.scalar (.int 1))) state)
  | rangeThree {start stop step : Lists.Value} :
      Invokes state .range ⟨[start, stop, step], []⟩ (fromExcept (checkedRange start stop step) state)
  | emptyBool : Invokes state .bool ⟨[], []⟩ (.ok (boolValue false) state)
  | emptyList : Invokes state .list ⟨[], []⟩ (allocate [] state)
  | emptyTuple : Invokes state .tuple ⟨[], []⟩ (allocateTuple [] state)
  | bool {value : Lists.Value} :
      Invokes state .bool ⟨[value], []⟩ (Outcome.resume (truth value state) fun flag =>
        pure (boolValue flag))
  | type {value : Lists.Value} : Invokes state .type ⟨[value], []⟩ (.ok (.string (typeName value)) state)
  | lenString {text : String} :
      Invokes state .len ⟨[.string text], []⟩ (.ok (countValue text.utf8ByteSize) state)
  | lenRange {span : RangeValue} :
      Invokes state .len ⟨[.range span], []⟩ (.ok (countValue span.length) state)
  | lenCollection {value : Lists.Value} {out : Outcome (List Lists.Value)} :
      (∀ text, value ≠ .string text) → (∀ span, value ≠ .range span) → Items .len state value out →
      Invokes state .len ⟨[value], []⟩ (Outcome.resume out fun elements =>
        pure (countValue elements.length))
  | list {value : Lists.Value} {out : Outcome (List Lists.Value)} :
      Items .list state value out → Invokes state .list ⟨[value], []⟩ (Outcome.resume out allocate)
  | tuple {value : Lists.Value} {out : Outcome (List Lists.Value)} :
      Items .tuple state value out → Invokes state .tuple ⟨[value], []⟩ (Outcome.resume out allocateTuple)

end Silmaril.Languages.Starlark.Functions.Builtins
