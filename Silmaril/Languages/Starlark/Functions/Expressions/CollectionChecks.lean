module

import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs

namespace Silmaril.Languages.Starlark.Functions.Lowering

open scoped Quote

private def marker : Binding := ⟨.local, "marker"⟩
private def argument : Binding := ⟨.local, "value"⟩
private def events : Binding := ⟨.global, "events"⟩
private def noteName : Binding := ⟨.global, "note"⟩
private def read (binding : Binding) : Lists.Expr := .read (.bound binding)
private def integer (value : Int) : Expr := .atom (.scalar (.int value))
private def string (value : String) : Expr := .atom (.string value)

private def program : Program := #[
  ⟨{ positional := [⟨marker, none⟩, ⟨argument, none⟩] }, [], [⟨events, events⟩],
    .seq (.total (.atomic (.eval (.append (read events) (read marker)))))
      (.returnExpr (.atom (read argument)))⟩]

private def note (n : Int) (value : Expr) : Expr :=
  .callPos (.atom (read noteName)) [integer n, value]

private def length (value : Expr) : Expr := .callPos (.atom (.builtin .len)) [value]

private def root : Lists.State := (({} : Lists.State).allocateSlot events).write marker (.scalar (.int 99))

private def setup : Body := .seq (.total (.atomic (.assign events (.list .empty)))) (.define noteName 0)

private def execute (expression : Expr) : Lists.Outcome Lists.Value :=
  Lists.Outcome.resume (run program setup root) fun _ => denoteExpr program [0] expression

private def integers (values : List Int) : List Lists.Value := values.map fun n => .scalar (.int n)

private def observed (state : Lists.State) (trace : List Int) : Bool :=
  decide (state.bindings marker = some (.scalar (.int 99)) ∧ state.slots marker = none) &&
    match state.bindingValue events with
    | .ok (.list address) => decide (state.heap[address]? = some ⟨.list (integers trace), false⟩)
    | _ => false

-- Each call runs once, and allocation keeps the values in element order.
#guard
  let expression := Expr.index (.list [note 1 (integer 17), note 2 (integer 22)]) (note 3 (integer (-1)))
  match execute expression with
  | .ok (.scalar (.int 22)) state =>
    observed state [1, 2, 3] && state.heap.any (fun cell => decide (cell.contents = .list (integers [17, 22])))
  | _ => false

-- The index operand mutates the receiver through an alias before the read.
#guard
  match execute (.index (note 1 (.atom (read events))) (note 2 (integer (-1)))) with
  | .ok (.scalar (.int 2)) state => observed state [1, 2]
  | _ => false

-- Failure stops later operands and leaves the display itself unallocated.
#guard
  let expression := Expr.list [note 1 (integer 17), length (note 2 (integer 9)), note 3 (integer 22)]
  match execute expression with
  | .error (.builtinType .len (.scalar (.int 9))) state =>
    observed state [1, 2] && (state.heap.toList.filter (fun cell => match cell.contents with
      | .list _ => true
      | _ => false)).length == 1
  | _ => false

#guard
  let failedReceiver := Expr.index (length (note 1 (integer 9))) (note 2 (integer 0))
  let failedOperand := Expr.index (.list [note 1 (integer 17)]) (length (note 2 (integer 9)))
  let badTarget := Expr.index (note 1 (integer 17)) (note 2 (integer 0))
  match execute failedReceiver, execute failedOperand, execute badTarget with
  | .error (.builtinType .len (.scalar (.int 9))) first,
    .error (.builtinType .len (.scalar (.int 9))) second, .error .indexTarget third =>
    observed first [1] && observed second [1, 2] && observed third [1, 2] &&
      second.heap.any (fun cell => decide (cell.contents = .list (integers [17])))
  | _, _, _ => false

-- The normalized source uses the same declaration and module evaluator as other expressions.
#guard
  let commands : List Modules.Resolve.Command := [
    .define "pick" { positional := [⟨"value", none⟩] } (.ret (some starlark%[value])),
    .define "driver" {} (.ret (some starlark%[[pick(17), pick(22),][pick(-1)]])),
    .assign "out" starlark%[driver()]]
  match Modules.Resolve.runModule commands (fun _ => none) {} with
  | .ok (.ok published _) => decide (published.exports.lookup "out" = some (.scalar (.int 22)))
  | _ => false

#guard
  let bad := Expr.call (.atom (.builtin .len)) [] [("x", integer 0), ("x", integer 1)] none none
  let expression := Expr.branch (integer 1) (integer 2) (.list [.index (.list []) bad])
  match runChecked program (.returnExpr expression) {} with
  | .error (.duplicateExplicitKeyword "x") => true
  | _ => false

#guard
  match execute (.tuple [note 1 (integer 17), note 2 (integer 22)]) with
  | .ok (.tuple address) state =>
    let key : Lists.Key := [.openTuple, .scalar (.int 17), .scalar (.int 22), .closeTuple]
    observed state [1, 2] && decide (state.heap[address]? = some ⟨.tuple (integers [17, 22]) (some key), false⟩)
  | _ => false

#guard
  match execute (.tuple [note 1 (integer 17), length (note 2 (integer 9)), note 3 (integer 22)]) with
  | .error (.builtinType .len (.scalar (.int 9))) state =>
    observed state [1, 2] && state.heap.all (fun cell => match cell.contents with
      | .tuple .. => false
      | _ => true)
  | _ => false

#guard
  let commands : List Modules.Resolve.Command := [
    .define "pick" { positional := [⟨"value", none⟩] } (.ret (some starlark%[value])),
    .assign "out" starlark%[(pick(17), pick(22),)[pick(-1)]]]
  match Modules.Resolve.runModule commands (fun _ => none) {} with
  | .ok (.ok published _) => decide (published.exports.lookup "out" = some (.scalar (.int 22)))
  | _ => false

private def dictionary (state : Lists.State) (entries : List (String × Int)) : Bool :=
  let expected := entries.map fun (name, value) =>
    (⟨.string name, [.string name], .scalar (.int value)⟩ : Lists.Entry)
  decide (state.heap[3]? = some ⟨.dict expected, false⟩)

private def pairs : List (Expr × Expr) := [
  (note 1 (string "b"), note 2 (integer 17)), (note 3 (string "a"), note 4 (integer 22))]

-- Allocation precedes the first operand. Each pair is inserted in source order.
#guard
  match execute (.dict pairs) with
  | .ok (.dict 3) state => observed state [1, 2, 3, 4] && dictionary state [("b", 17), ("a", 22)]
  | _ => false

#guard
  let later := (note 7 (string "later"), note 8 (integer 9))
  let duplicate := (note 5 (string "b"), note 6 (integer 33))
  match execute (.dict (pairs ++ [duplicate, later])) with
  | .error (.duplicateKey (.string "b")) state =>
    observed state [1, 2, 3, 4, 5, 6] && dictionary state [("b", 17), ("a", 22)]
  | _ => false

#guard
  let bad := (note 5 (.list []), note 6 (integer 9))
  let later := (note 7 (string "later"), note 8 (integer 9))
  match execute (.dict (pairs ++ [bad, later])) with
  | .error (.unhashableKey (.list address)) state =>
    observed state [1, 2, 3, 4, 5, 6] && dictionary state [("b", 17), ("a", 22)] &&
      address > 3 && decide (state.heap[address]? = some ⟨.list [], false⟩)
  | _ => false

-- An operand error takes precedence over entry validation and keeps the allocated dictionary.
#guard
  let keyError := Expr.dict [(length (note 1 (integer 9)), note 2 (integer 17))]
  let valueError := Expr.dict [(note 1 (.list []), length (note 2 (integer 9)))]
  match execute keyError, execute valueError with
  | .error (.builtinType .len (.scalar (.int 9))) first, .error (.builtinType .len (.scalar (.int 9))) second =>
    observed first [1] && observed second [1, 2] && dictionary first [] && dictionary second []
  | _, _ => false

#guard
  let duplicate := (note 5 (string "b"), note 6 (integer 33))
  let expression := Expr.dict (pairs ++ [duplicate, (note 7 (string "later"), note 8 (integer 9))])
  let target : Binding := ⟨.global, "out"⟩
  match execute expression, run program (.seq setup (lower expression target 5).code) root with
  | .error (.duplicateKey (.string "b")) direct, .error (.duplicateKey (.string "b")) lowered =>
    decide (lowered.heap = direct.heap) && observed lowered [1, 2, 3, 4, 5, 6] &&
      match lowered.bindingValue target with
      | .error (.uninitialized binding) => binding == target
      | _ => false
  | _, _ => false

#guard
  let commands : List Modules.Resolve.Command := [
    .define "pick" { positional := [⟨"value", none⟩] } (.ret (some starlark%[value])),
    .assign "out" starlark%[{ (pick(7),) : pick(22), }[(pick(7),)]]]
  match Modules.Resolve.runModule commands (fun _ => none) {} with
  | .ok (.ok published _) => decide (published.exports.lookup "out" = some (.scalar (.int 22)))
  | _ => false

private def omitted : Expr := .atom (.scalar .none)

private def onlyEventsList (state : Lists.State) : Bool :=
  state.heap.toList.countP (fun cell => match cell.contents with
    | .list _ => true
    | _ => false) == 1

-- The slice reads after the bound effects, including those on its own receiver.
#guard
  let expression := Expr.slice (note 1 (.atom (read events))) (note 2 omitted)
    (note 3 omitted) (note 4 (integer (-2)))
  let target : Binding := ⟨.global, "out"⟩
  match execute expression, run program (.seq setup (lower expression target 5).code) root with
  | .ok (.list address) direct, .ok .next lowered =>
    observed direct [1, 2, 3, 4] && observed lowered [1, 2, 3, 4] &&
      decide ((direct.bindingValue events).toOption ≠ some (.list address) ∧
        direct.heap[address]? = some ⟨.list (integers [4, 2]), false⟩ ∧
        lowered.heap = direct.heap ∧ (lowered.bindingValue target).toOption = some (.list address))
  | _, _ => false

#guard
  let slice := fun start stop stride => (Lists.sliceElements (integers [0, 1, 2, 3, 4]) start stop stride).toOption
  let noneValue : Lists.Value := .scalar .none
  let intValue := fun i => Lists.Value.scalar (.int i)
  decide (slice (intValue (-4)) (intValue (-1)) (intValue 2) = some (integers [1, 3]) ∧
    slice (intValue 100) (intValue (-100)) (intValue (-2)) = some (integers [4, 2, 0]) ∧
    slice noneValue (intValue (-1)) (intValue (-1)) = some [] ∧
    slice (intValue (-100)) noneValue (intValue (-1)) = some [] ∧
    slice (intValue (-100000000000)) (intValue 100000000000) (intValue 100000000000) = some (integers [0]) ∧
    (Lists.sliceElements ([] : List Lists.Value) noneValue noneValue (intValue (-1))).toOption = some [])

-- Empty slices still allocate mutable list cells, even when read from a frozen source.
#guard
  let source : Lists.Cell := ⟨.list (integers [7]), true⟩
  let state : Lists.State := { heap := #[source] }
  match Lists.readSlice (.list 0) (.scalar .none) (.scalar (.int 0)) (.scalar .none) state with
  | .ok (.list address) next =>
    decide (address = 1 ∧ next.heap = #[source, ⟨.list [], false⟩])
  | _ => false

-- A failure in a bound skips later operands and the allocation. The lowered destination stays unbound.
#guard
  let expression := Expr.slice (note 1 (.atom (read events))) (length (note 2 (integer 9)))
    (note 3 omitted) (note 4 (integer 1))
  let target : Binding := ⟨.global, "out"⟩
  match execute expression, run program (.seq setup (lower expression target 5).code) root with
  | .error (.builtinType .len (.scalar (.int 9))) direct, .error (.builtinType .len (.scalar (.int 9))) lowered =>
    observed direct [1, 2] && observed lowered [1, 2] &&
      onlyEventsList direct && decide (lowered.heap = direct.heap) &&
      match lowered.bindingValue target with
      | .error (.uninitialized binding) => binding == target
      | _ => false
  | _, _ => false

-- A later operand failure takes precedence over receiver or bound validation.
#guard
  let bad := Expr.atom (.scalar (.bool true))
  match execute (.slice (note 1 (integer 42)) (note 2 bad) (length (note 3 (integer 9)))
      (note 4 (integer 0))) with
  | .error (.builtinType .len (.scalar (.int 9))) state => observed state [1, 2, 3] && onlyEventsList state
  | _ => false

-- Validation waits for the operands. Receiver, stride, start and stop are then checked in order.
#guard
  let readEvents := Expr.atom (read events)
  let bad := Expr.atom (.scalar (.bool true))
  let failed := fun receiver start stop stride expected =>
    match execute (.slice (note 1 receiver) (note 2 start) (note 3 stop) (note 4 stride)) with
    | .error error state => error == expected && observed state [1, 2, 3, 4] && onlyEventsList state
    | _ => false
  failed (integer 42) bad bad (integer 0) .sliceTarget &&
    failed readEvents bad bad bad (.sliceStrideType (.scalar (.bool true))) &&
    failed readEvents bad bad (integer 0) .zeroSliceStride &&
    failed readEvents bad bad omitted (.sliceStartType (.scalar (.bool true))) &&
    failed readEvents omitted bad omitted (.sliceStopType (.scalar (.bool true)))

-- A normalized function returns a fresh outer list whose nested values still alias the original.
#guard
  let commands : List Modules.Resolve.Command := [
    .define "pick" { positional := [⟨"value", none⟩] } (.ret (some starlark%[value])),
    .assign "inner" starlark%[[7]], .assign "items" starlark%[[inner, [8]]],
    .define "driver" {} (.ret (some starlark%[pick(items)[pick(None) :: pick(-1)]])),
    .assign "out" starlark%[driver()],
    .setIndex starlark%[inner] starlark%[0] starlark%[42],
    .setIndex starlark%[out] starlark%[0] starlark%[None],
    .assign "shared" starlark%[out[1][0]], .assign "untouched" starlark%[items[1][0]],
    .assign "tupleKey" starlark%[{(0, 1, 2)[pick(1):] : 9}[(1, 2)]]]
  match Modules.Resolve.runModule commands (fun _ => none) {} with
  | .ok (.ok published state) =>
    match published.exports.lookup "inner", published.exports.lookup "items", published.exports.lookup "out" with
    | some (.list inner), some (.list items), some (.list out) =>
      decide (items ≠ out ∧ state.heap[out]? = some ⟨.list [.scalar .none, .list inner], true⟩ ∧
        published.exports.lookup "shared" = some (.scalar (.int 42)) ∧
        published.exports.lookup "untouched" = some (.scalar (.int 8)) ∧
        published.exports.lookup "tupleKey" = some (.scalar (.int 9)))
    | _, _, _ => false
  | _ => false

-- Slicing selects UTF-8 bytes, then checks that the selected byte sequence is valid.
#guard
  let check := fun expression expected => match execute expression with
    | .ok (.string text) _ => text == expected
    | _ => false
  check (.slice (string "aé🙂z") (integer 1) (integer (-1)) omitted) "é🙂" &&
    check (.slice (string "aéz") omitted omitted (integer (-3))) "za" &&
    check (.slice (string "banana") (integer 4) omitted (integer (-2))) "nnb" &&
    check (.slice (string "é") (integer 1) (integer 1) omitted) ""

#guard
  let slice := Expr.slice (string "é")
  let invalid := fun expression => match execute expression with
    | .error .invalidSliceUTF8 _ => true
    | _ => false
  invalid (slice (integer 0) (integer 1) omitted) &&
    invalid (slice omitted omitted (integer (-1)))

-- All operand effects survive UTF-8 validation failure. Lowering skips the destination write.
#guard
  let expression := Expr.slice (note 1 (string "aé🙂z")) (note 2 (integer 1))
    (note 3 (integer 2)) (note 4 omitted)
  let target : Binding := ⟨.global, "out"⟩
  match execute expression, run program (.seq setup (lower expression target 5).code) root with
  | .error .invalidSliceUTF8 direct, .error .invalidSliceUTF8 lowered =>
    observed direct [1, 2, 3, 4] && observed lowered [1, 2, 3, 4] &&
      decide (lowered.heap = direct.heap) &&
      match lowered.bindingValue target with
      | .error (.uninitialized binding) => binding == target
      | _ => false
  | _, _ => false

-- A later evaluation or bound validation error takes precedence over decoding.
#guard
  let receiver := note 1 (string "é")
  let start := note 2 (integer 0)
  let stop := note 3 (integer 1)
  match execute (.slice receiver start stop (length (note 4 (integer 9)))),
      execute (.slice receiver start stop (note 4 (integer 0))) with
  | .error (.builtinType .len (.scalar (.int 9))) first, .error .zeroSliceStride second =>
    observed first [1, 2, 3, 4] && observed second [1, 2, 3, 4]
  | _, _ => false

-- A string result uses no heap cell, and the existing len observes the selected byte count.
#guard
  let initial : Lists.State := { iterators := [0], heap := #[⟨.list [], false⟩] }
  let commands : List Modules.Resolve.Command := [
    .define "pick" { positional := [⟨"value", none⟩] } (.ret (some starlark%[value])),
    .define "take" {} (.ret (some starlark%[pick("aé🙂z")[pick(1):pick(-1)]])),
    .assign "out" starlark%[take()], .assign "size" starlark%[len(out)]]
  match Lists.readSlice (.string "aé🙂z") (.scalar (.int 1)) (.scalar (.int (-1))) (.scalar .none) initial,
      Modules.Resolve.runModule commands (fun _ => none) {} with
  | .ok (.string "é🙂") next, .ok (.ok published _) =>
    decide (next.heap = initial.heap ∧ next.iterators = initial.iterators ∧
      published.exports.lookup "out" = some (.string "é🙂") ∧
      published.exports.lookup "size" = some (.scalar (.int 6)))
  | _, _ => false

-- The first and last bytes of a multibyte string can still be ASCII.
#guard
  let initial : Lists.State := { iterators := [0], heap := #[⟨.list [], false⟩] }
  let check := fun text index expected =>
    match Lists.readIndex (.string text) (.scalar (.int index)) initial with
    | .ok (.string value) next =>
      value == expected && decide (next.heap = initial.heap ∧ next.iterators = initial.iterators)
    | _ => false
  check "abc" 1 "b" && check "abc" (-1) "c" &&
    check "aé🙂z" (-8) "a" && check "aé🙂z" 7 "z"

#guard
  let check := fun text index expected =>
    match execute (.index (string text) index) with
    | .error error _ => error == expected
    | _ => false
  check "aé🙂z" (integer 1) .invalidIndexUTF8 &&
    check "aé🙂z" (integer (-6)) .invalidIndexUTF8 &&
    check "aé🙂z" (integer 8) (.indexRange 8 8) &&
    check "aé🙂z" (integer (-9)) (.indexRange (-9) 8) &&
    check "aé🙂z" (integer 2147483648) (.indexRange 2147483648 8) &&
    check "" (integer 0) (.indexRange 0 0)

-- Successful and malformed one-byte reads both preserve preceding call effects.
#guard
  let target : Binding := ⟨.global, "out"⟩
  let check := fun subscript =>
    let expression := Expr.index (note 1 (string "éz")) (note 2 (integer subscript))
    let initial := root.write target (.string "old")
    (execute expression, run program (.seq setup (lower expression target 5).code) initial)
  match check (-1), check 0 with
  | (.ok (.string "z") success, .ok .next loweredSuccess),
    (.error .invalidIndexUTF8 failure, .error .invalidIndexUTF8 loweredFailure) =>
    observed success [1, 2] && observed failure [1, 2] &&
      observed loweredSuccess [1, 2] && observed loweredFailure [1, 2] &&
      decide (success.heap = loweredSuccess.heap ∧ failure.heap = loweredFailure.heap ∧
        (loweredSuccess.bindingValue target).toOption = some (.string "z") ∧
        (loweredFailure.bindingValue target).toOption = some (.string "old"))
  | _, _ => false

-- Receiver and index evaluation precede dispatch. Dispatch precedes index type checking.
#guard
  let bad := Expr.atom (.scalar (.bool true))
  let failed := fun receiver index expected trace =>
    match execute (.index receiver index) with
    | .error error state => error == expected && observed state trace
    | _ => false
  let badCall := fun marker => length (note marker (integer 9))
  let callError := Lists.Error.builtinType .len (.scalar (.int 9))
  failed (badCall 1) (note 2 bad) callError [1] &&
    failed (note 1 (integer 42)) (badCall 2) callError [1, 2] &&
    failed (note 1 (integer 42)) (note 2 bad) .indexTarget [1, 2] &&
    failed (note 1 (string "é")) (note 2 bad) .indexType [1, 2]

#guard
  let commands : List Modules.Resolve.Command := [
    .define "pick" { positional := [⟨"value", none⟩] } (.ret (some starlark%[value])),
    .define "last" {} (.ret (some starlark%[pick("aé🙂z")[pick(-1)]])),
    .assign "out" starlark%[last()]]
  match Modules.Resolve.runModule commands (fun _ => none) {} with
  | .ok (.ok published _) => decide (published.exports.lookup "out" = some (.string "z"))
  | _ => false

private def rangeExpr (args : List Expr) : Expr := .callPos (.atom (.builtin .range)) args

#guard
  let check := fun args subscript expected =>
    match execute (.index (rangeExpr (args.map integer)) (integer subscript)) with
    | .ok (.scalar (.int value)) _ => value == expected
    | _ => false
  check [5] 0 0 && check [3, 8] (-1) 7 &&
    check [3, 10, 2] (-4) 3 && check [10, 3, -2] (-1) 4 &&
    check [3000000000] 2147483648 2147483648 &&
    check [9223372036854775808] (-1) 9223372036854775807 &&
    check [-9223372036854775808, 9223372036854775807] 0 (-9223372036854775808) &&
    check [-9223372036854775808, 9223372036854775807] (-1) 9223372036854775806

-- A large exact range and its indexed result use no heap cells.
#guard
  let program : Program := #[]
  let initial : Lists.State := { iterators := [0], heap := #[⟨.list [], false⟩] }
  let expression := Expr.index (rangeExpr [integer 1000000000000000000000000]) (integer (-1))
  match denoteExpr program [] expression initial with
  | .ok (.scalar (.int 999999999999999999999999)) next =>
    decide (next.heap = initial.heap ∧ next.iterators = initial.iterators)
  | _ => false

#guard
  let target : Binding := ⟨.global, "out"⟩
  let check := fun subscript =>
    let receiver := note 1 (rangeExpr [integer 10, integer 3, integer (-2)])
    let expression := Expr.index receiver (note 2 (integer subscript))
    let initial := root.write target (.scalar (.int 99))
    (execute expression, run program (.seq setup (lower expression target 5).code) initial)
  match check (-1), check (-5) with
  | (.ok (.scalar (.int 4)) success, .ok .next loweredSuccess),
    (.error (.indexRange (-5) 4) failure, .error (.indexRange (-5) 4) loweredFailure) =>
    observed success [1, 2] && observed failure [1, 2] &&
      observed loweredSuccess [1, 2] && observed loweredFailure [1, 2] &&
      decide (success.heap = loweredSuccess.heap ∧ failure.heap = loweredFailure.heap ∧
        (loweredSuccess.bindingValue target).toOption = some (.scalar (.int 4)) ∧
        (loweredFailure.bindingValue target).toOption = some (.scalar (.int 99)))
  | _, _ => false

-- All constructor argument effects precede validation. A failed receiver skips the subscript.
#guard
  let bad := Expr.atom (.scalar (.bool true))
  let failed := fun receiver subscript expected trace =>
    match execute (.index receiver subscript) with
    | .error error state => error == expected && observed state trace
    | _ => false
  let subscript := note 4 (integer 0)
  let base := rangeExpr [integer 4]
  failed (rangeExpr [note 1 (integer 1), note 2 (integer 2), note 3 (integer 0)])
    subscript .zeroRangeStep [1, 2, 3] &&
  failed (rangeExpr [note 1 bad, note 2 (string "wrong"), note 3 (integer 0)])
    subscript (.builtinType .range (.scalar (.bool true))) [1, 2, 3] &&
  failed (rangeExpr [note 1 bad, note 2 (integer 2), note 3 (integer 3), note 4 (integer 4)])
    (note 5 (integer 0)) (.builtinArity .range 1 3 4) [1, 2, 3, 4] &&
  failed (rangeExpr []) subscript (.builtinArity .range 1 3 0) [] &&
  failed (.call (.atom (.builtin .range)) [] [("start", note 1 (integer 0)), ("stop", note 2 (integer 3))] none none)
    subscript (.builtinKeyword .range "start") [1, 2] &&
  failed (note 1 base) (length (note 2 (integer 9))) (.builtinType .len (.scalar (.int 9))) [1, 2] &&
  failed (note 1 base) (note 2 bad) .indexType [1, 2] &&
  failed (note 1 base) (note 2 (integer 4)) (.indexRange 4 4) [1, 2] &&
  failed (note 1 (rangeExpr [integer 2, integer 4, integer (-1)])) (note 2 (integer 0)) (.indexRange 0 0) [1, 2]

#guard
  let commands : List Modules.Resolve.Command := [
    .define "pick" { positional := [⟨"value", none⟩] } (.ret (some starlark%[value])),
    .define "last" {} (.ret (some starlark%[pick(range(pick(10), 3, -2))[pick(-1)]])),
    .assign "out" starlark%[last()], .assign "size" starlark%[len(range(10, 3, -2))],
    .assign "empty" starlark%[bool(range(1, 1))], .assign "kind" starlark%[type(range(1))]]
  match Modules.Resolve.runModule commands (fun _ => none) {} with
  | .ok (.ok published _) =>
    decide (published.exports.lookup "out" = some (.scalar (.int 4)) ∧
      published.exports.lookup "size" = some (.scalar (.int 4)) ∧
      published.exports.lookup "empty" = some (.scalar (.bool false)) ∧
      published.exports.lookup "kind" = some (.string "range"))
  | _ => false

-- Slices of descending ranges and nested slices are still ranges.
#guard
  let check := fun expression count first last =>
    match execute expression with
    | .ok value@(.range span) state =>
      match Lists.readIndex value (.scalar (.int 0)) state, Lists.readIndex value (.scalar (.int (-1))) state with
      | .ok (.scalar (.int a)) _, .ok (.scalar (.int b)) _ => span.length == count && a == first && b == last
      | _, _ => false
    | _ => false
  let descending := Expr.slice (rangeExpr [integer 10, integer 1, integer (-2)]) omitted omitted (integer (-2))
  let inner := Expr.slice (rangeExpr [integer 2, integer 30, integer 3]) (integer 1) (integer 10) (integer 3)
  check descending 3 2 10 && check (.slice inner omitted omitted (integer (-2))) 2 23 5

-- An explicit reverse stop of -1 differs from omission. Empty slices stay empty.
#guard
  let source := rangeExpr [integer 6]
  let check := fun expression =>
    match execute (.index expression (integer 0)) with
    | .error (.indexRange 0 0) _ => true
    | _ => false
  let crossed := Expr.slice source (integer 4) (integer 1) omitted
  check (.slice source omitted (integer (-1)) (integer (-1))) &&
    check (.slice crossed omitted omitted (integer (-1))) &&
    check (.slice (rangeExpr [integer 0]) omitted omitted (integer (-1)))

-- Point reads and length remain exact even when offsets or composed endpoints exceed Go's width.
#guard
  let initial : Lists.State := { iterators := [0], heap := #[⟨.list [], false⟩] }
  let check := fun expression count last =>
    match denoteExpr #[] [] expression initial with
    | .ok value@(.range span) next =>
      match Lists.readIndex value (.scalar (.int (-1))) next with
      | .ok (.scalar (.int result)) final =>
        span.length == count && result == last &&
          decide (next.heap = initial.heap ∧ final.heap = initial.heap ∧ final.iterators = initial.iterators)
      | _ => false
    | _ => false
  check (.slice (rangeExpr [integer 1000000000000000000000000]) omitted omitted (integer (-2)))
    500000000000000000000000 1 &&
  check (.slice (rangeExpr [integer 10]) (integer (-100000000000)) (integer 100000000000) (integer 100000000000))
    1 0 &&
  check (.slice (rangeExpr [integer 0, integer 9223372036854775807, integer 4611686018427387904])
    omitted (integer 1) (integer 2)) 1 0 &&
  check (.slice (rangeExpr [integer 9223372036854775806, integer 9223372036854775807, integer 2])
    omitted omitted omitted) 1 9223372036854775806

-- Scratch lowering preserves the slice value and effects, and the old destination after failure.
#guard
  let target : Binding := ⟨.global, "out"⟩
  let initial := root.write target (.scalar (.int 99))
  let receiver := note 1 (rangeExpr [integer 10])
  let check := fun start stop stride =>
    let expression := Expr.slice receiver (note 2 start) (note 3 stop) (note 4 stride)
    (execute expression, run program (.seq setup (lower expression target 5).code) initial)
  let bad := Expr.atom (.scalar (.bool true))
  match check (integer 1) (integer 8) (integer 3), check bad bad (integer 0) with
  | (.ok value@(.range span) success, .ok .next loweredSuccess),
    (.error .zeroSliceStride failure, .error .zeroSliceStride loweredFailure) =>
    decide (span.start = 1 ∧ span.stop = 8 ∧ span.step = 3 ∧ span.length = 3) &&
      observed success [1, 2, 3, 4] && observed failure [1, 2, 3, 4] &&
      observed loweredSuccess [1, 2, 3, 4] && observed loweredFailure [1, 2, 3, 4] &&
      decide (success.heap = loweredSuccess.heap ∧ failure.heap = loweredFailure.heap ∧
        (loweredSuccess.bindingValue target).toOption = some value ∧
        (loweredFailure.bindingValue target).toOption = some (.scalar (.int 99)))
  | _, _ => false

#guard
  let receiver := note 1 (rangeExpr [integer 10])
  let badValue := Lists.Value.scalar (.bool true)
  let bad := Expr.atom (.scalar (.bool true))
  let failed := fun expression expected trace =>
    match execute expression with
    | .error error state => error == expected && observed state trace
    | _ => false
  failed (.slice receiver (note 2 bad) (length (note 3 (integer 9))) (note 4 (integer 0)))
    (.builtinType .len (.scalar (.int 9))) [1, 2, 3] &&
  failed (.slice receiver (note 2 bad) (note 3 bad) (note 4 bad)) (.sliceStrideType badValue) [1, 2, 3, 4] &&
  failed (.slice receiver (note 2 bad) (note 3 bad) (note 4 omitted)) (.sliceStartType badValue) [1, 2, 3, 4] &&
  failed (.slice receiver (note 2 omitted) (note 3 bad) (note 4 (integer (-1)))) (.sliceStopType badValue) [1, 2, 3, 4]

#guard
  let commands : List Modules.Resolve.Command := [
    .define "pick" { positional := [⟨"value", none⟩] } (.ret (some starlark%[value])),
    .define "nested" {} (.ret (some starlark%[pick(range(2, 30, 3))[pick(1):pick(10):pick(3)][pick(None)::pick(-2)]])),
    .assign "items" starlark%[nested()], .assign "first" starlark%[items[0]],
    .assign "last" starlark%[items[-1]], .assign "size" starlark%[len(items)]]
  match Modules.Resolve.runModule commands (fun _ => none) {} with
  | .ok (.ok published _) =>
    decide (published.exports.lookup "first" = some (.scalar (.int 23)) ∧
      published.exports.lookup "last" = some (.scalar (.int 5)) ∧
      published.exports.lookup "size" = some (.scalar (.int 2)))
  | _ => false

-- Ordinary calls stage a range-producing operand once before materialization.
#guard
  let destination : Binding := ⟨.global, "out"⟩
  let initial := root.write destination (.scalar (.int 99))
  let span := rangeExpr [integer 10, integer 3, integer (-2)]
  let sliced := Expr.slice span omitted omitted (integer (-2))
  let expression := Expr.callPos (.atom (.builtin .tuple)) [note 1 sliced]
  let runLowered := fun expr => run program (.seq setup (lower expr destination 5).code) initial
  let bad := Expr.call (.atom (.builtin .list)) [note 1 span, note 2 (integer 0)]
    [("ignored", note 3 (integer 0))] none none
  match execute expression, runLowered expression, execute bad, runLowered bad, execute (note 1 sliced) with
  | .ok tuple@(.tuple address) direct, .ok .next lowered,
    .error (.builtinKeyword .list "ignored") failure, .error (.builtinKeyword .list "ignored") loweredFailure,
    .ok _ operand =>
      observed direct [1] && observed failure [1, 2, 3] &&
        decide (address = operand.heap.size ∧ direct.heap.size = operand.heap.size + 1 ∧
          direct.heap = lowered.heap ∧ failure.heap = loweredFailure.heap ∧
          direct.iterators = lowered.iterators ∧ failure.iterators = loweredFailure.iterators ∧
          (lowered.bindingValue destination).toOption = some tuple ∧
          (loweredFailure.bindingValue destination).toOption = some (.scalar (.int 99))) &&
        match Lists.tupleElements address direct with
        | .ok values _ => decide (values = integers [4, 8])
        | .error _ _ => false
  | _, _, _, _, _ => false

#guard
  let span := rangeExpr [integer 4]
  let failed := fun expression expected events =>
    match execute expression with
    | .error error state =>
      error == expected && observed state events &&
        state.heap.toList.countP (fun cell => match cell.contents with
          | .list _ | .tuple .. => true
          | _ => false) == 1
    | _ => false
  failed (.callPos (.atom (.builtin .list)) [note 1 span, length (note 2 (integer 9)), note 3 span])
    (.builtinType .len (.scalar (.int 9))) [1, 2] &&
  failed (.callPos (.atom (.builtin .tuple)) [note 1 (integer 9), note 2 span])
    (.builtinArity .tuple 0 1 2) [1, 2] &&
  failed (.callPos (.atom (.builtin .list)) [note 1 (integer 9)]) (.builtinType .list (.scalar (.int 9))) [1]

#guard
  let commands : List Modules.Resolve.Command := [
    .assign "empty_list" starlark%[len(list(range(0)))],
    .assign "empty_tuple" starlark%[len(tuple(range(3, 1)))],
    .assign "descending" starlark%[list(range(10, 3, -2))[1]],
    .assign "lookup" starlark%[{tuple(range(10, 3, -2)[::-2]): "sliced"}[(4, 8)]]]
  match Modules.Resolve.runModule commands (fun _ => none) {} with
  | .ok (.ok published _) =>
    decide (published.exports.lookup "empty_list" = some (.scalar (.int 0)) ∧
      published.exports.lookup "empty_tuple" = some (.scalar (.int 0)) ∧
      published.exports.lookup "descending" = some (.scalar (.int 8)) ∧
      published.exports.lookup "lookup" = some (.string "sliced"))
  | _ => false

-- Both operands run before mapping validation. A valid mapping exposes the
-- arity error. If evaluating the range fails, the mapping operand is skipped.
#guard
  let destination : Binding := ⟨.global, "out"⟩
  let initial := root.write destination (.scalar (.int 99))
  let span := rangeExpr [integer 5, integer 1, integer (-2)]
  let check := fun rangeOperand mapping expected trace =>
    let expression := Expr.call (note 0 (.atom (.builtin .type))) [] []
      (some rangeOperand) (some (note 2 mapping))
    match execute expression, run program (.seq setup (lower expression destination 5).code) initial with
    | .error error direct, .error loweredError lowered =>
      error == expected && loweredError == expected && observed direct trace &&
        decide (direct.heap = lowered.heap ∧ direct.iterators = lowered.iterators ∧
          (lowered.bindingValue destination).toOption = some (.scalar (.int 99)))
    | _, _ => false
  check (note 1 span) (.list []) .invalidStarStar [0, 1, 2] &&
    check (note 1 span) (.dict []) (.builtinArity .type 1 1 2) [0, 1, 2] &&
    check (rangeExpr [note 1 (integer 0), integer 4, integer 0]) (.list []) .zeroRangeStep [0, 1]

#guard
  let pack : Modules.Resolve.Command := .define "pack"
    { positional := [⟨"a", some starlark%[7]⟩], varargs := some "rest"
      keywordOnly := [⟨"tag", some starlark%["default"]⟩] }
    (.ret (some starlark%[(a, rest, tag)]))
  let commands : List Modules.Resolve.Command := [pack,
    .assign "empty" starlark%[{(7, (), "default"): True}[pack(*range(0))]],
    .assign "descending" starlark%[{(10, (8, 6, 4), "default"): True}[pack(*range(10, 3, -2))]],
    .assign "mixed" starlark%[{(9, (4, 8), "mixed"): True}[pack(9, tag="mixed", *range(10, 3, -2)[::-2])]]]
  match Modules.Resolve.runModule commands (fun _ => none) {} with
  | .ok (.ok published _) =>
    ["empty", "descending", "mixed"].all fun name =>
      decide (published.exports.lookup name = some (.scalar (.bool true)))
  | _ => false

end Silmaril.Languages.Starlark.Functions.Lowering
