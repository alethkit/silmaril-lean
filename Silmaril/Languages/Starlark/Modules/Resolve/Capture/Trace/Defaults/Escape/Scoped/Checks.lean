module

import Batteries.Data.Except
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped

open scoped Functions.Lowering.Quote
open Assignment (LexicalBlock)
open Bindings.WithDefaults (Callable)
open Lists (State Cell)

private def maker (fails : Bool) : Spec :=
  ⟨⟨"make", "seed", "inner", [], [("early", .list 13),
      ("saved", if fails then .read "offset" else .parameter), ("last", .list 73)], "answer", 0⟩,
    [("picked", starlark%[saved[offset]]), ("buffer", starlark%[[picked]]),
      ("answer", starlark%[buffer[seed]]), ("repeat_read", starlark%[saved[offset]])], [], [("offset", 0), ("unused", 42), ("offset", 1)]⟩

private def commands (fails : Bool) : List Command :=
  [(maker fails).command, .assign "seed_a" starlark%[[3, 5]], .assign "seed_b" starlark%[[6, 8]],
    invocation "make" "a" [starlark%[seed_a]], invocation "make" "b" [starlark%[seed_b]],
    .assign "alias" starlark%[a], invocation "alias" "first" [], invocation "b" "second" [],
    .assign "replacement" starlark%[[7, 9]], invocation "a" "override" [starlark%[0], starlark%[replacement]],
    invocation "alias" "again" []]

private theorem admitted (fails : Bool) : Bindings.WithDefaults.Profile (commands fails) := by
  let globals := names (commands fails)
  have known {name : String}
      (member : name ∈ ["make", "seed_a", "seed_b", "a", "b", "alias",
        "first", "second", "replacement", "override", "again"]) : Visible globals name := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      cases fails <;> unfold Visible <;> decide +revert
  let spec := maker fails
  let locals := ["picked", "buffer", "answer", "repeat_read"]
  let owned := ["early", "saved", "last", "picked", "buffer", "answer", "repeat_read"]
  let block : LexicalBlock := ⟨spec.child.parameters.names ++ locals, spec.enclosing, globals⟩
  have inBlock {name : String} (member : name ∈ owned) : name ∈ block.owned := by
    cases fails <;> exact member
  have localOrigin {name : String} (member : name ∈ owned) : ReadOrigin block (fileSlot name) .owned :=
    .owned (inBlock member)
  have localRead (name : String) (member : name ∈ owned) (legal : name.toList.head? ≠ some '$') :
      Defaults.Body.Operand block (.scalar (.read name)) (Leaf.readOperand (fileSlot name)) [fileSlot name] :=
    .read legal (.owned (inBlock member)) (localOrigin member)
  have outsideBlock {name : String} (outside : name ∉ owned) : name ∉ block.owned := by
    cases fails <;> exact outside
  have outerOrigin {name : String} (outside : name ∉ owned) (member : name ∈ ["seed", "inner", "offset", "unused"]) :
      ReadOrigin block (fileSlot name) .enclosing :=
    .enclosing (outsideBlock outside) member
  have outerRead (name : String) (outside : name ∉ owned) (member : name ∈ ["seed", "inner", "offset", "unused"])
      (legal : name.toList.head? ≠ some '$') :
      Defaults.Body.Operand block (.scalar (.read name)) (Leaf.readOperand (fileSlot name)) [fileSlot name] :=
    .read legal (.enclosing (outsideBlock outside) member) (outerOrigin outside member)
  have wrapper : Admitted globals spec := by
    have wrapperNames : Escape.WrapperNames spec.wrapper := by
      cases fails <;> exact ⟨by decide, by decide, by decide⟩
    have childFresh : spec.wrapper.childName ∉ spec.additional := by change "inner" ∉ ([] : List String); decide
    refine ⟨⟨wrapperNames, childFresh, ?_, ?_⟩, ?_⟩
    · intro name member
      change name ∈ ["offset", "unused", "offset"] at member
      simp at member
      rcases member with rfl | rfl | rfl <;> cases fails <;> decide
    · intro name present
      obtain ⟨target, present⟩ := present
      cases fails
      · simp [spec, maker] at present
      · simp [spec, maker] at present
        obtain ⟨_, rfl⟩ := present
        decide
    · have pick := Defaults.Body.Operand.index (localRead "saved" (by decide) (by decide))
        (outerRead "offset" (by decide) (by decide) (by decide))
      have code := Defaults.Body.Elaborates.assign (block := block) (name := "picked") (inBlock (by decide)) pick
        (.assign (name := "buffer") (inBlock (by decide)) (.list (localRead "picked" (by decide) (by decide)))
          (.assign (name := "answer") (inBlock (by decide))
            (.index (localRead "buffer" (by decide) (by decide)) (outerRead "seed" (by decide) (by decide) (by decide)))
            (.assign (name := "repeat_read") (inBlock (by decide)) pick
              (.ret (localRead "answer" (by decide) (by decide))))))
      let entries : List Functions.FreeName :=
        [⟨fileSlot "offset", fileSlot "offset"⟩, ⟨fileSlot "seed", fileSlot "seed"⟩]
      have selects : Selects block
          [fileSlot "saved", fileSlot "offset", fileSlot "picked", fileSlot "buffer", fileSlot "seed",
            fileSlot "saved", fileSlot "offset", fileSlot "answer"]
          entries := by
        apply Selects.owned (localOrigin (name := "saved") (by decide))
        apply Selects.enclosing (outerOrigin (name := "offset") (by decide) (by decide))
        apply Selects.owned (localOrigin (name := "picked") (by decide))
        apply Selects.owned (localOrigin (name := "buffer") (by decide))
        apply Selects.enclosing (outerOrigin (name := "seed") (by decide) (by decide))
        exact .owned (localOrigin (name := "answer") (by decide)) .nil
      have binders : Block.LocalBinders spec.child.parameters.names spec.child.body.binders locals := by
        cases fails <;> exact .keep (by decide) (.keep (by decide) (.keep (by decide) (.keep (by decide) .nil)))
      refine ⟨⟨⟨locals, _, _, entries, binders, code, selects⟩, ?_⟩⟩
      intro entry member
      change entry ∈ entries at member
      simp [entries] at member
      rcases member with rfl | rfl
      · exact ⟨"offset", by change "offset" ∈ ["seed", "offset", "unused", "offset"]; decide, rfl⟩
      · exact ⟨"seed", by change "seed" ∈ ["seed", "offset", "unused", "offset"]; decide, rfl⟩
  have pair (first second : Int) : Initializer globals (.list [.scalar (.int first), .scalar (.int second)]) :=
    .list (by intro item member; simp at member; rcases member with rfl | rfl <;> exact .int _)
  have read {name : String} (visible : Visible globals name) :
      ∀ argument ∈ [(.scalar (.read name) : Functions.Lowering.Resolve.SourceExpr)], Trace.Operand globals argument := by
    intro argument present
    simp at present
    subst argument
    exact .read visible
  have overrideArgs : ∀ argument ∈ [starlark%[0], starlark%[replacement]], Trace.Operand globals argument := by
    intro argument present
    simp at present
    rcases present with rfl | rfl
    · exact .int 0
    · exact .read (known (by decide))
  let parent := Callable.nestedBody spec
  let escaped := Callable.sequenced spec.child
  change Bindings.WithDefaults.Schedule globals (fun _ => none) (commands fails)
  unfold commands
  exact .define (body := parent) (known (name := "make") (by decide)) wrapper
    (.setup (known (by decide)) (pair 3 5) (.setup (known (by decide)) (pair 6 8)
      (.invoke (body := parent) (known (by decide)) (known (by decide)) rfl (read (known (by decide)))
        (.invoke (body := parent) (known (by decide)) (known (by decide)) rfl (read (known (by decide)))
          (.copy (body := escaped) (known (by decide)) (known (by decide)) rfl
            (.invoke (body := escaped) (known (by decide)) (known (by decide)) rfl (by simp)
              (.invoke (body := escaped) (known (by decide)) (known (by decide)) rfl (by simp)
                (.setup (known (by decide)) (pair 7 9)
                  (.invoke (body := escaped) (known (by decide)) (known (by decide)) rfl overrideArgs
                    (.invoke (body := escaped) (known (by decide)) (known (by decide)) rfl (by simp) (.nil _)))))))))))

private def caller : State := { bindings := fun _ => some (.scalar (.int 99)), iterators := [123] }

example (fails : Bool) {resolved : ResolvedModule} (checked : resolve (commands fails) = .ok resolved) :
    ∃ out publication,
      Wrapper.ReachedPrefix (Bindings.WithDefaults.Step resolved (names (commands fails))) 0
        (enter resolved.source caller) (commands fails) out ∧
      Leaf.Finishes (names (commands fails)) caller out publication ∧
      Initializes (commands fails) (fun _ => none) caller #[] (.ok publication) ∧
      runModule (commands fails) (fun _ => none) caller = .ok publication :=
  Bindings.WithDefaults.checked_module (admitted fails) checked (fun _ => none) caller

private def captureAddresses (heap : Array Cell) (closure seed : Lists.Value) : Option (List Nat) := do
  let .function address := closure | none
  let ⟨.function child, true⟩ ← heap[address]? | none
  let [first, second] := child.captures | none
  let [(early, .list allocated), (saved, savedValue), (last, .list later)] := child.defaults | none
  if child.declaration == 0 && early == fileSlot "early" && saved == fileSlot "saved" && savedValue == seed &&
      last == fileSlot "last" && heap[allocated]? == some ⟨.list [.scalar (.int 13)], true⟩ &&
      heap[later]? == some ⟨.list [.scalar (.int 73)], true⟩ &&
      first.binding == fileSlot "offset" && first.localCell &&
      second.binding == fileSlot "seed" && second.localCell &&
      heap[first.address]? == some ⟨.binding (some (.scalar (.int 1))), true⟩ &&
      heap[second.address]? == some ⟨.binding (some (.scalar (.int 0))), true⟩ then
    some [first.address, second.address]
  else none

#guard
  match resolve (commands false), runModule (commands false) (fun _ => none) caller with
  | .ok resolved, .ok (.ok published final) =>
    let entered := (enter resolved.source caller).heap.size
    let get name := published.exports.lookup name
    match get "a", get "b", get "seed_a", get "seed_b" with
    | some a, some b, some (.list seedA), some (.list seedB) =>
      (resolved.program[1]?.map Functions.Declaration.locals) ==
        some [fileSlot "inner", fileSlot "offset", fileSlot "unused"] &&
      get "alias" == some a && a != b &&
      get "first" == some (.scalar (.int 5)) && get "second" == some (.scalar (.int 8)) &&
      get "override" == some (.scalar (.int 9)) && get "again" == some (.scalar (.int 5)) &&
      final.heap[seedA]? == some ⟨.list [.scalar (.int 3), .scalar (.int 5)], true⟩ &&
      final.heap[seedB]? == some ⟨.list [.scalar (.int 6), .scalar (.int 8)], true⟩ &&
      captureAddresses final.heap a (.list seedA) == some [entered + 5, entered + 3] &&
      captureAddresses final.heap b (.list seedB) == some [entered + 12, entered + 10] &&
      final.bindingValue (globalSlot "first") == .ok (.scalar (.int 99)) && final.iterators == [123]
    | _, _, _, _ => false
  | _, _ => false

#guard
  match resolve (commands true), runModule (commands true) (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime (.uninitialized name)) final) =>
    let initial := enter resolved.source caller
    let get (name : String) : Option Lists.Contents :=
      match initial.slots (globalSlot name) with
      | some (.owned address) => final.heap[address]?.map Cell.contents
      | _ => none
    let active := initial.heap.size + 3
    name == fileSlot "offset" && final.heap.size == active + 5 &&
    (["a", "b", "alias", "first", "second", "replacement", "override", "again"] : List String).all
      (fun name => get name == some (.binding none)) &&
    final.heap[active]? == some ⟨.binding (some (.list (active - 2))), false⟩ &&
    final.heap[active - 2]? == some ⟨.list [.scalar (.int 3), .scalar (.int 5)], false⟩ &&
    ([1, 2, 3] : List Nat).all (fun index => final.heap[active + index]? == some ⟨.binding none, false⟩) &&
    final.heap[active + 4]? == some ⟨.list [.scalar (.int 13)], false⟩ &&
    final.bindingValue (globalSlot "a") == .ok (.scalar (.int 99)) && final.iterators == [123]
  | _, _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped
