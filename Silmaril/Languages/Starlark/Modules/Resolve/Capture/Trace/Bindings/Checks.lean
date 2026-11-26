module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings

open scoped Functions.Lowering.Quote
open Lists (State Cell)

private def inner : Forwarding.Chain :=
  .mixed "first" ["idx"] ⟨"idx", starlark%[box], starlark%[idx], .plain starlark%[pair_one], starlark%[seen]⟩

private def maker : Forwarding.Chain := .wrapper "maker" ["box"] inner

private def second : Forwarding.Chain :=
  .mixed "second" ["idx"] ⟨"idx", starlark%[shared], starlark%[idx], .plain starlark%[pair_two], starlark%[later]⟩

private def defineRoot (chain : Forwarding.Chain) : Command :=
  .define chain.name (.required chain.parameters) chain.body

private def following : List Command :=
  [.assign "part2" starlark%[second(1)], .assign "part3" starlark%[copy(1)]]

private def later : Command := .assign "later" starlark%[14]

private def commands (initialized : Bool) : List Command :=
  [defineRoot maker, .assign "box" starlark%[[3]], .assign "shared" starlark%[box],
    .assign "one" starlark%[maker(shared)], .assign "copy" starlark%[one], defineRoot second,
    .assign "pair_one" starlark%[(0, 9)], .assign "pair_two" starlark%[(0, 12)], .assign "seen" starlark%[13],
    .assign "part1" starlark%[one(1)]] ++
    if initialized then later :: following else following ++ [later]

private theorem admitted (initialized : Bool) : Bindings.Profile (commands initialized) := by
  let globals := names (commands initialized)
  have known (name : String) (present : name ∈ ["maker", "box", "shared", "one", "copy", "second",
        "pair_one", "pair_two", "seen", "part1", "part2", "part3", "later"]) : Visible globals name := by
    cases initialized <;>
      simp [Visible, globals, commands, names, defineRoot, following, later, maker, second,
        Forwarding.Chain.name] at * <;>
      rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have parameters : ∀ name ∈ ["idx"], name.toList.head? ≠ some '$' := by
    intro name member
    simp at member
    subst name
    decide
  have firstCode : Definitions globals [] maker := by
    refine .wrapper (by intro name member; simp at member; subst name; decide) (by decide)
      (.mixed parameters (by decide) ?_ ?_ ?_ ?_)
    all_goals cases initialized <;> simp [Visible, globals, commands, names, defineRoot, following, later,
      maker, inner, second, Forwarding.Chain.name]
  have secondCode : Definitions globals [] second := by
    refine .mixed parameters (by decide) ?_ ?_ ?_ ?_
    all_goals cases initialized <;> simp [Visible, globals, commands, names, defineRoot, following, later,
      maker, second, Forwarding.Chain.name]
  have oneArg : ∀ arg ∈ [starlark%[1]], Operand globals arg := by
    intro arg member
    simp at member
    subst arg
    exact .int 1
  have pairOperand (secondValue : Int) :
      Initializer globals (.tuple [.scalar (.int 0), .scalar (.int secondValue)]) := by
    apply Initializer.tuple
    intro operand member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .int 0
    · exact .int secondValue
  have listOperand : Initializer globals starlark%[[3]] := by
    apply Initializer.list
    intro arg member
    simp at member
    subst arg
    exact .int 3
  change Schedule globals (fun _ => none) (commands initialized)
  unfold commands
  refine .define (chain := maker) (known "maker" (by decide)) firstCode
    (.setup (known "box" (by decide)) listOperand
    (.setup (known "shared" (by decide)) (.operand (.read (known "box" (by decide))))
    (.wrapper (known "maker" (by decide)) (known "one" (by decide)) rfl ?_
    (.copy (known "one" (by decide)) (known "copy" (by decide)) rfl
    (.define (chain := second) (known "second" (by decide)) secondCode
    (.setup (known "pair_one" (by decide)) (pairOperand 9)
    (.setup (known "pair_two" (by decide)) (pairOperand 12)
    (.setup (known "seen" (by decide)) (.operand (.int 13))
    (.leaf (known "one" (by decide)) (known "part1" (by decide)) rfl oneArg ?_)))))))))
  · intro arg member
    simp at member
    subst arg
    exact .read (known "shared" (by decide))
  · cases initialized with
    | false =>
      exact .leaf (known "second" (by decide)) (known "part2" (by decide)) rfl oneArg
        (.leaf (known "copy" (by decide)) (known "part3" (by decide)) rfl oneArg
          (.setup (known "later" (by decide)) (.operand (.int 14)) (.nil _)))
    | true =>
      exact .setup (known "later" (by decide)) (.operand (.int 14))
        (.leaf (known "second" (by decide)) (known "part2" (by decide)) rfl oneArg
          (.leaf (known "copy" (by decide)) (known "part3" (by decide)) rfl oneArg (.nil _)))

-- The theorem supplies the trace and exact observation from both static
-- command orders, including the call after the unrelated definition.
example (initialized : Bool) {resolved : ResolvedModule}
    (checked : resolve (commands initialized) = .ok resolved) :
    ∃ out observation,
      Wrapper.ReachedPrefix (Leaf.Step resolved (names (commands initialized))) 0
        (enter resolved.source {}) (commands initialized) out ∧
      Leaf.Finishes (names (commands initialized)) {} out observation ∧
      Initializes (commands initialized) (fun _ => none) {} #[] (.ok observation) ∧
      runModule (commands initialized) (fun _ => none) {} = .ok observation :=
  checked_module (admitted initialized) checked (fun _ => none) {}

private def caller : State := {
  bindings := fun _ => some (.scalar (.int 99))
  iterators := [123]
}

#guard
  match runModule (commands true) (fun _ => none) caller with
  | .ok (.ok published final) =>
    match published.exports.lookup "box", published.exports.lookup "one", published.exports.lookup "second" with
    | some (.list box), some (.function escaped), some (.function independent) =>
      published.exports.map Prod.fst ==
        ["maker", "box", "shared", "one", "copy", "second", "pair_one", "pair_two", "seen", "part1", "later", "part2", "part3"] &&
      published.exports.lookup "shared" == some (.list box) &&
      published.exports.lookup "copy" == some (.function escaped) &&
      published.exports.lookup "part1" == some (.scalar (.int 13)) &&
      published.exports.lookup "part2" == some (.scalar (.int 14)) &&
      published.exports.lookup "part3" == some (.scalar (.int 13)) &&
      final.heap[box]? == some ⟨.list [.scalar (.int 9)], true⟩ &&
      (match final.heap[escaped]?, final.heap[independent]? with
      | some ⟨.function first, true⟩, some ⟨.function second, true⟩ => first.declaration == 0 && second.declaration == 2
      | _, _ => false) &&
      final.iterators == [123]
    | _, _, _ => false
  | _ => false

#guard
  match resolve (commands false), runModule (commands false) (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime (.uninitialized slot)) final) =>
    let initial := enter resolved.source caller
    let value := fun name => match initial.slots (globalSlot name) with
      | some (.owned address) => final.heap[address]?.map Cell.contents
      | _ => none
    slot == globalSlot "later" && value "part1" == some (.binding (some (.scalar (.int 13)))) &&
      value "part2" == some (.binding none) && value "part3" == some (.binding none) &&
      value "later" == some (.binding none) &&
      final.heap.any (fun cell => cell == ⟨.list [.scalar (.int 12)], false⟩) &&
      final.bindingValue (globalSlot "box") == .ok (.scalar (.int 99)) && final.iterators == [123]
  | _, _ => false

-- The callable environment models a write to the live binding. Checked
-- normalized modules retain the pinned prohibition on duplicate globals.
#guard
  match resolve (commands true ++ [.assign "one" starlark%[second]]) with
  | .error (.validation (.bindingCollision "one")) => true
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings
