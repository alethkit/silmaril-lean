module

import Silmaril.Languages.Starlark.Lists.Thms
meta import Silmaril.Languages.Starlark.Lists.Denotation.Defs

namespace Silmaril.Languages.Starlark.Lists.Comparison

deriving instance DecidableEq for Except

private def int (n : Int) : Value := .scalar (.int n)

private def result {α : Type} : Outcome α → Except Error α
  | .ok value _ => .ok value
  | .error error _ => .error error

private def item (key : String) (value : Value) : Entry := ⟨.string key, [.string key], value⟩

-- Distinct insertion positions and numeric key spellings match through the
-- table lookup. The reached values nest dictionaries, tuples and lists.
#guard
  let action : Meaning (List (Except Error Bool)) := do
    let smallLeft ← allocateDict [item "n" (int 0)]
    let smallRight ← allocateDict [item "n" (.scalar (.float 0x8000000000000000))]
    let xs ← allocate [smallLeft, int 3]
    let ys ← allocate [smallRight, .scalar (.float 0x4008000000000000)]
    let tx ← allocateTuple [xs]
    let ty ← allocateTuple [ys]
    let lhs ← allocateDict []
    let rhs ← allocateDict []
    let key := int 9007199254740992
    let floatKey : Value := .scalar (.float 0x4340000000000000)
    let flag : Value := .scalar (.bool false)
    writeIndex lhs key tx
    writeIndex lhs flag (int 1)
    writeIndex rhs flag (int 1)
    writeIndex rhs floatKey ty
    let before ← fun state => .ok (evaluate state.heap .eq lhs rhs) state
    writeIndex lhs floatKey (int 7)
    fun state => .ok [before, evaluate state.heap .eq lhs rhs, evaluate state.heap .ne lhs rhs] state
  result (action {}) = .ok [.ok true, .ok false, .ok true]

-- Size, a missing key and the first unequal value can each mask a cycle.
-- Reversing the operands changes which entry the scan reaches first.
#guard
  let state : State := { heap := #[
    ⟨.dict [item "self" (.dict 0)], false⟩,
    ⟨.dict [item "self" (.dict 1)], false⟩,
    ⟨.dict [item "guard" (int 0), item "cycle" (.dict 0)], false⟩,
    ⟨.dict [item "cycle" (.dict 1), item "guard" (int 1)], false⟩,
    ⟨.dict [item "missing" (int 0), item "cycle" (.dict 0)], false⟩,
    ⟨.dict [], false⟩,
    ⟨.list [], false⟩] }
  evaluate state.heap .eq (.dict 0) (.dict 5) = .ok false ∧
    evaluate state.heap .eq (.dict 0) (.dict 0) = .error .comparisonDepth ∧
    evaluate state.heap .eq (.dict 2) (.dict 3) = .ok false ∧
    evaluate state.heap .eq (.dict 3) (.dict 2) = .error .comparisonDepth ∧
    evaluate state.heap .eq (.dict 4) (.dict 3) = .ok false ∧
    evaluate state.heap .ne (.dict 3) (.dict 4) = .error .comparisonDepth ∧
    evaluate state.heap .eq (.dict 42) (.dict 6) = .error (.danglingAddress 42) ∧
    evaluate state.heap .eq (.dict 5) (.dict 6) = .error (.wrongCellKind 6) ∧
    evaluate state.heap .eq (.dict 5) (.list 6) = .ok false ∧
    evaluate state.heap .mem (int 1) (.dict 5) = .error (.membershipTarget (.dict 5))

-- Values consume the same budget through dictionary entries. Cached keys
-- match independently of the remaining depth of the value comparison.
#guard
  let action : Meaning (List (Except Error Bool)) := do
    let wrap := fun count (value : Value) =>
      (List.range count).foldlM (fun field _ => allocateDict [item "n" field]) value
    let nine ← wrap 9 (int 0)
    let nineFloat ← wrap 9 (.scalar (.float 0x8000000000000000))
    let ten ← allocateDict [item "n" nine]
    let tenFloat ← allocateDict [item "n" nineFloat]
    let keyWrap := fun (leaf : Value) =>
      (List.range 10).foldlM (fun key _ => allocateTuple [key]) leaf
    let key ← keyWrap (int 0)
    let floatKey ← keyWrap (.scalar (.float 0x8000000000000000))
    let lhs ← allocateDict []
    let rhs ← allocateDict []
    writeIndex lhs key (int 1)
    writeIndex rhs floatKey (int 1)
    let cached ← fun state => .ok (evaluate state.heap .eq lhs rhs) state
    writeIndex lhs key lhs
    writeIndex rhs floatKey rhs
    fun state => .ok [evaluate state.heap .eq nine nineFloat, evaluate state.heap .eq ten tenFloat,
      cached, evaluate state.heap .eq lhs rhs, equalAt state.heap 1 (.dict 0) (.dict 0)] state
  result (action {}) = .ok [.ok true, .error .comparisonDepth, .ok true,
    .error .comparisonDepth, .error .comparisonDepth]

private def actual : Binding := ⟨.global, "actual"⟩
private def expected : Binding := ⟨.global, "expected"⟩
private def events : Binding := ⟨.global, "events"⟩

private def initial : State :=
  { heap := #[⟨.list [int 1], false⟩, ⟨.list [int 1, int 2], false⟩,
      ⟨.dict [item "events" (.list 0)], false⟩, ⟨.dict [item "events" (.list 1)], false⟩]
    bindings := fun name => if name = actual then some (.dict 2)
      else if name = expected then some (.dict 3)
      else if name = events then some (.list 0) else none }

-- The right operand mutates a value reachable from the already evaluated
-- left dictionary. The comparison reads both dictionaries in the reached heap.
example :
    let mark : Expr := .append (.read (.bound events)) (.scalar (.int 2))
    let right : Expr := .index (.tuple (.cons mark (.cons (.read (.bound expected)) .empty)))
      (.scalar (.int 1))
    denote (.compare .eq (.read (.bound actual)) right) initial =
      .ok (.scalar (.bool true)) { initial with heap := #[
        ⟨.list [int 1, int 2], false⟩, ⟨.list [int 1, int 2], false⟩,
        ⟨.dict [item "events" (.list 0)], false⟩, ⟨.dict [item "events" (.list 1)], false⟩,
        ⟨.tuple [.scalar .none, .dict 3] none, false⟩] } := rfl

end Silmaril.Languages.Starlark.Lists.Comparison
