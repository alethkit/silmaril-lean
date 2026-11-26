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

private inductive End where
  | success | prefixError | defaultError

private def firstIndex : End → Int
  | .prefixError => 1
  | _ => 0

private def defaultName : End → String
  | .defaultError => "unused"
  | _ => "offset"

private def maker (ending : End) : Spec :=
  ⟨⟨"make", "seed", "inner", [], [("early", .list 14),
      ("saved", .read (defaultName ending)), ("last", .list 73)], "answer", 0⟩,
    [("picked", starlark%[saved[offset]]), ("buffer", starlark%[[picked]]),
      ("answer", starlark%[buffer[seed]]), ("repeat_read", starlark%[saved[offset]])],
    [], [("offset", 0), ("unused", 42), ("offset", 1)],
    [("earlier", starlark%[[13]]), ("offset", .index starlark%[seed] (.scalar (.int (firstIndex ending))))]⟩

private def commands (ending : End) : List Command :=
  [(maker ending).command, .assign "seed_a" starlark%[[3, 5]], .assign "seed_b" starlark%[[6, 8]],
    .assign "outer_a" starlark%[[seed_a]], .assign "outer_b" starlark%[[seed_b]],
    invocation "make" "a" [starlark%[outer_a]], invocation "make" "b" [starlark%[outer_b]],
    .assign "alias" starlark%[a], invocation "alias" "first" [], invocation "b" "second" [],
    .assign "replacement" starlark%[[7, 9]], invocation "a" "override" [starlark%[0], starlark%[replacement]],
    invocation "alias" "again" []]

private theorem admitted (ending : End) : Bindings.WithDefaults.Profile (commands ending) := by
  let globals := names (commands ending)
  have known {name : String}
      (member : name ∈ ["make", "seed_a", "seed_b", "outer_a", "outer_b", "a", "b", "alias",
        "first", "second", "replacement", "override", "again"]) : Visible globals name := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      cases ending <;> unfold Visible <;> decide +revert
  let spec := maker ending
  let locals := ["picked", "buffer", "answer", "repeat_read"]
  let owned := ["early", "saved", "last", "picked", "buffer", "answer", "repeat_read"]
  let block : LexicalBlock := ⟨spec.child.parameters.names ++ locals, spec.enclosing, globals⟩
  have inBlock {name : String} (member : name ∈ owned) : name ∈ block.owned := by
    cases ending <;> exact member
  have localOrigin {name : String} (member : name ∈ owned) : ReadOrigin block (fileSlot name) .owned :=
    .owned (inBlock member)
  have localRead (name : String) (member : name ∈ owned) (legal : name.toList.head? ≠ some '$') :
      Defaults.Body.Operand block (.scalar (.read name)) (Leaf.readOperand (fileSlot name)) [fileSlot name] :=
    .read legal (.owned (inBlock member)) (localOrigin member)
  have outsideBlock {name : String} (outside : name ∉ owned) : name ∉ block.owned := by
    cases ending <;> exact outside
  have outerOrigin {name : String} (outside : name ∉ owned) (member : name ∈ ["seed", "earlier", "offset", "inner", "unused"]) :
      ReadOrigin block (fileSlot name) .enclosing :=
    .enclosing (outsideBlock outside) member
  have outerRead (name : String) (outside : name ∉ owned) (member : name ∈ ["seed", "earlier", "offset", "inner", "unused"])
      (legal : name.toList.head? ≠ some '$') :
      Defaults.Body.Operand block (.scalar (.read name)) (Leaf.readOperand (fileSlot name)) [fileSlot name] :=
    .read legal (.enclosing (outsideBlock outside) member) (outerOrigin outside member)
  have wrapper : Admitted globals spec := by
    have wrapperNames : Escape.WrapperNames spec.wrapper := by
      cases ending <;> exact ⟨by decide, by decide, by decide⟩
    have childFresh : spec.wrapper.childName ∉ spec.additional := by change "inner" ∉ ([] : List String); decide
    refine ⟨⟨wrapperNames, childFresh, ?_, ?_⟩, ?_⟩
    · intro name member
      change name ∈ ["offset", "unused", "offset"] at member
      simp at member
      rcases member with rfl | rfl | rfl <;> cases ending <;> decide
    · intro name present
      obtain ⟨target, present⟩ := present
      have equal : target = "saved" ∧ name = defaultName ending := by
        simpa [spec, maker] using present
      rw [equal.2]
      cases ending <;> decide
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
        cases ending <;> exact .keep (by decide) (.keep (by decide) (.keep (by decide) (.keep (by decide) .nil)))
      have member {name : String} (known : name ∈ ["seed", "earlier", "offset", "inner", "unused"]) :
          name ∈ (spec.block globals).owned := known
      have seed : Defaults.Body.Operand (spec.block globals) starlark%[seed]
          (Leaf.readOperand (fileSlot "seed")) [fileSlot "seed"] :=
        .read (by decide) (.owned (member (by decide))) (.owned (member (by decide)))
      have leading := Defaults.Body.ElaboratesPrefix.cons (name := "earlier") (member (by decide)) (.list (.int 13))
        (.cons (name := "offset") (member (by decide)) (.index seed (.int (firstIndex ending))) .nil)
      refine ⟨⟨⟨locals, _, _, entries, binders, code, selects⟩, ?_, _, [fileSlot "seed"], leading, ?_⟩⟩
      · intro entry present
        change entry ∈ entries at present
        simp [entries] at present
        rcases present with rfl | rfl
        · exact ⟨"offset", member (by decide), by change "offset" ≠ "inner"; decide, rfl⟩
        · exact ⟨"seed", member (by decide), by change "seed" ≠ "inner"; decide, rfl⟩
      · intro binding present
        have same := List.mem_singleton.mp present
        exact ⟨"seed", member (by decide), same⟩
  have pair (first second : Int) : Initializer globals (.list [.scalar (.int first), .scalar (.int second)]) :=
    .list (by intro item member; simp at member; rcases member with rfl | rfl <;> exact .int _)
  have read {name : String} (visible : Visible globals name) :
      ∀ argument ∈ [(.scalar (.read name) : Functions.Lowering.Resolve.SourceExpr)], Trace.Operand globals argument := by
    intro argument present
    simp at present
    subst argument
    exact .read visible
  have singleton {name : String} (visible : Visible globals name) : Initializer globals (.list [.scalar (.read name)]) :=
    .list (read visible)
  have overrideArgs : ∀ argument ∈ [starlark%[0], starlark%[replacement]], Trace.Operand globals argument := by
    intro argument present
    simp at present
    rcases present with rfl | rfl
    · exact .int 0
    · exact .read (known (by decide))
  let parent := Callable.nestedBody spec
  let escaped := Callable.sequenced spec.child
  change Bindings.WithDefaults.Schedule globals (fun _ => none) (commands ending)
  unfold commands
  exact .define (body := parent) (known (name := "make") (by decide)) wrapper
    (.setup (known (by decide)) (pair 3 5) (.setup (known (by decide)) (pair 6 8)
      (.setup (known (by decide)) (singleton (known (by decide)))
      (.setup (known (by decide)) (singleton (known (by decide)))
      (.invoke (body := parent) (known (by decide)) (known (by decide)) rfl (read (known (by decide)))
        (.invoke (body := parent) (known (by decide)) (known (by decide)) rfl (read (known (by decide)))
          (.copy (body := escaped) (known (by decide)) (known (by decide)) rfl
            (.invoke (body := escaped) (known (by decide)) (known (by decide)) rfl (by simp)
              (.invoke (body := escaped) (known (by decide)) (known (by decide)) rfl (by simp)
                (.setup (known (by decide)) (pair 7 9)
                  (.invoke (body := escaped) (known (by decide)) (known (by decide)) rfl overrideArgs
                    (.invoke (body := escaped) (known (by decide)) (known (by decide)) rfl (by simp) (.nil _)))))))))))))

private def caller : State := { bindings := fun _ => some (.scalar (.int 99)), iterators := [123] }

example (ending : End) {resolved : ResolvedModule} (checked : resolve (commands ending) = .ok resolved) :
    ∃ out publication,
      Wrapper.ReachedPrefix (Bindings.WithDefaults.Step resolved (names (commands ending))) 0
        (enter resolved.source caller) (commands ending) out ∧
      Leaf.Finishes (names (commands ending)) caller out publication ∧
      Initializes (commands ending) (fun _ => none) caller #[] (.ok publication) ∧
      runModule (commands ending) (fun _ => none) caller = .ok publication :=
  Bindings.WithDefaults.checked_module (admitted ending) checked (fun _ => none) caller

private def captureAddresses (heap : Array Cell) (closure seed : Lists.Value) : Option (List Nat) := do
  let .function address := closure | none
  let ⟨.function child, true⟩ ← heap[address]? | none
  let [first, second] := child.captures | none
  let [(early, .list allocated), (saved, savedValue), (last, .list later)] := child.defaults | none
  if child.declaration == 0 && early == fileSlot "early" && saved == fileSlot "saved" && savedValue == seed &&
      last == fileSlot "last" && heap[allocated]? == some ⟨.list [.scalar (.int 14)], true⟩ &&
      heap[later]? == some ⟨.list [.scalar (.int 73)], true⟩ &&
      first.binding == fileSlot "offset" && first.localCell &&
      second.binding == fileSlot "seed" && second.localCell &&
      heap[first.address]? == some ⟨.binding (some (.scalar (.int 1))), true⟩ &&
      heap[second.address]? == some ⟨.binding (some (.scalar (.int 0))), true⟩ then
    some [first.address, second.address]
  else none

#guard
  match resolve (commands .success), runModule (commands .success) (fun _ => none) caller with
  | .ok resolved, .ok (.ok published final) =>
    let entered := (enter resolved.source caller).heap.size
    let get name := published.exports.lookup name
    match get "a", get "b", get "seed_a", get "seed_b" with
    | some a, some b, some (.list seedA), some (.list seedB) =>
      (resolved.program[1]?.map Functions.Declaration.locals) ==
        some [fileSlot "earlier", fileSlot "offset", fileSlot "inner", fileSlot "unused"] &&
      get "alias" == some a && a != b &&
      get "first" == some (.scalar (.int 5)) && get "second" == some (.scalar (.int 8)) &&
      get "override" == some (.scalar (.int 9)) && get "again" == some (.scalar (.int 5)) &&
      final.heap[seedA]? == some ⟨.list [.scalar (.int 3), .scalar (.int 5)], true⟩ &&
      final.heap[seedB]? == some ⟨.list [.scalar (.int 6), .scalar (.int 8)], true⟩ &&
      captureAddresses final.heap a (.list seedA) == some [entered + 7, entered + 5] &&
      captureAddresses final.heap b (.list seedB) == some [entered + 16, entered + 14] &&
      final.bindingValue (globalSlot "first") == .ok (.scalar (.int 99)) && final.iterators == [123]
    | _, _, _, _ => false
  | _, _ => false

private def errorControl (ending : End) (expected : Lists.Error) (reachedDefault : Bool) : Bool :=
  match resolve (commands ending), runModule (commands ending) (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime error) final) =>
    let initial := enter resolved.source caller
    let get (name : String) : Option Lists.Contents :=
      match initial.slots (globalSlot name) with
      | some (.owned address) => final.heap[address]?.map Cell.contents
      | _ => none
    let active := initial.heap.size + 5
    error == expected && final.heap.size == active + (if reachedDefault then 7 else 6) &&
    (["a", "b", "alias", "first", "second", "replacement", "override", "again"] : List String).all
      (fun name => get name == some (.binding none)) &&
    final.heap[active]? == some ⟨.binding (some (.list (active - 2))), false⟩ &&
    final.heap[active - 4]? == some ⟨.list [.scalar (.int 3), .scalar (.int 5)], false⟩ &&
    final.heap[active + 1]? == some ⟨.binding (some (.list (active + 5))), false⟩ &&
    final.heap[active + 2]? == some ⟨.binding (if reachedDefault then some (.list (active - 4)) else none), false⟩ &&
    final.heap[active + 3]? == some ⟨.binding none, false⟩ &&
    final.heap[active + 4]? == some ⟨.binding none, false⟩ &&
    final.heap[active + 5]? == some ⟨.list [.scalar (.int 13)], false⟩ &&
    final.heap[active + 6]? == (if reachedDefault then some ⟨.list [.scalar (.int 14)], false⟩ else none) &&
    final.bindingValue (globalSlot "a") == .ok (.scalar (.int 99)) && final.iterators == [123]
  | _, _ => false

#guard errorControl .prefixError (.indexRange 1 1) false
#guard errorControl .defaultError (.uninitialized (fileSlot "unused")) true

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped
