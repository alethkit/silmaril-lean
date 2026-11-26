module

import Batteries.Data.Except
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults

open scoped Functions.Lowering.Quote
open Lists (State Cell)

private def pick : Callable := .defaulted
  ⟨"pick", ⟨["required"], [("value", starlark%[seed]), ("buffer", starlark%[[1]])]⟩, "value"⟩

private def edit : Callable := .required
  (.mixed "edit" ["index"] ⟨"index", starlark%[seed], starlark%[index], .plain starlark%[patch], starlark%[index]⟩)

private inductive End where
  | success | operand | surplus | missing

private def arguments : End → List Functions.Lowering.Resolve.SourceExpr
  | .success => [starlark%[0]]
  | .operand => [starlark%[0], starlark%[seed[1]], starlark%[2], starlark%[later]]
  | .surplus => [starlark%[0], starlark%[1], starlark%[2], starlark%[3]]
  | .missing => []

private def commands (ending : End) : List Command :=
  [.assign "seed" starlark%[[3]], pick.command, .assign "saved" starlark%[pick],
    invocation "saved" "first" [starlark%[0]], edit.command, .assign "patch" starlark%[(0, 8)],
    invocation "edit" "touched" [starlark%[1]], .assign "replacement" starlark%[[4]],
    invocation "saved" "override" [starlark%[0], starlark%[replacement]],
    invocation "saved" "again" (arguments ending), .assign "later" starlark%[77]]

private theorem literalList {globals : List String} (n : Int) :
    Initializer globals (.list [.scalar (.int n)]) :=
  .list (by intro item h; simp at h; subst item; exact .int _)

private theorem admitted (ending : End) : Profile (commands ending) := by
  let globals := names (commands ending)
  have known {name : String} (member : name ∈
      ["seed", "pick", "saved", "first", "edit", "patch", "touched", "replacement", "override", "again", "later"]) :
      Visible globals name := by
    change name ∈ names (commands ending) ∧ _
    constructor
    · exact member
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have pickOk : pick.Admitted globals := by
    change Trace.Defaults.Admitted globals _
    refine ⟨?_, by unfold Visible; decide⟩
    intro item present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact .operand (.read (known (by decide)))
    · exact literalList 1
  have editOk : edit.Admitted globals := by
    change Definitions globals [] _
    refine .mixed (by intro name h; simp at h; subst name; decide) (by decide) ?_ ?_ ?_ ?_
    all_goals simp [Visible, globals, commands, names, pick, edit, invocation, Callable.command,
      Defaults.Definition.command, root, Forwarding.Chain.name]
  have oneArg : ∀ arg ∈ [starlark%[0]], Operand globals arg := by
    intro arg h
    simp at h
    subst arg
    exact .int _
  have editArg : ∀ arg ∈ [starlark%[1]], Operand globals arg := by
    intro arg h
    simp at h
    subst arg
    exact .int _
  have overrideArg : ∀ arg ∈ [starlark%[0], starlark%[replacement]], Operand globals arg := by
    intro arg h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact .int _
    · exact .read (known (by decide))
  have endArgs : ∀ arg ∈ arguments ending, Operand globals arg := by
    intro arg h
    cases ending with
    | success => exact oneArg _ h
    | missing => cases h
    | operand =>
      simp only [arguments, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact .int _
      · exact .index (.read (known (by decide))) (.int 1)
      · exact .int _
      · exact .read (known (by decide))
    | surplus =>
      simp only [arguments, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> exact .int _
  have patchOk : Initializer globals starlark%[(0, 8)] := by
    apply Initializer.tuple
    intro arg h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact .int _
  change Schedule globals (fun _ => none) (commands ending)
  unfold commands
  refine .setup (known (by decide)) (literalList 3) (.define (body := pick) (known (by decide)) pickOk
    (.copy (known (by decide)) (known (by decide)) rfl
    (.invoke (body := pick) (known (by decide)) (known (by decide)) rfl oneArg
    (.define (body := edit) (known (by decide)) editOk
    (.setup (known (by decide)) patchOk
    (.invoke (body := edit) (known (by decide)) (known (by decide)) rfl editArg
    (.setup (known (by decide)) (literalList 4)
    (.invoke (body := pick) (known (by decide)) (known (by decide)) rfl overrideArg
    (.invoke (body := pick) (known (by decide)) (known (by decide)) rfl endArgs
    (.setup (known (by decide)) (.operand (.int 77)) (.nil _)))))))))))

private def caller : State := { bindings := fun _ => some (.scalar (.int 99)), iterators := [123] }

example (ending : End) {resolved : ResolvedModule} (checked : resolve (commands ending) = .ok resolved) :
    ∃ out publication,
      Wrapper.ReachedPrefix (Step resolved (names (commands ending))) 0
        (enter resolved.source caller) (commands ending) out ∧
      Leaf.Finishes (names (commands ending)) caller out publication ∧
      Initializes (commands ending) (fun _ => none) caller #[] (.ok publication) ∧
      runModule (commands ending) (fun _ => none) caller = .ok publication :=
  checked_module (admitted ending) checked (fun _ => none) caller

#guard
  match runModule (commands .success) (fun _ => none) caller with
  | .ok (.ok published final) =>
    let get := fun name => published.exports.lookup name
    match get "seed", get "pick", get "edit" with
    | some (.list seed), some (.function pick), some (.function edit) =>
      published.exports.map Prod.fst == ["seed", "pick", "saved", "first", "edit", "patch", "touched",
        "replacement", "override", "again", "later"] &&
      get "saved" == get "pick" && get "first" == get "seed" && get "again" == get "seed" &&
      get "override" == get "replacement" && get "touched" == some (.scalar (.int 0)) &&
      final.heap[seed]? == some ⟨.list [.scalar (.int 8)], true⟩ &&
      (match final.heap[pick]?, final.heap[edit]? with
       | some ⟨.function defaulted, true⟩, some ⟨.function ordinary, true⟩ =>
         defaulted.declaration == 0 && ordinary.declaration == 1 &&
         (match defaulted.defaults with
          | [(_, .list saved), (_, .list buffer)] =>
            saved == seed && final.heap[buffer]? == some ⟨.list [.scalar (.int 1)], true⟩ &&
            (final.heap.filter (fun cell => cell.contents == .list [.scalar (.int 1)])).size == 1
          | _ => false)
       | _, _ => false) && final.iterators == [123]
    | _, _, _ => false
  | _ => false

private def errorControl (ending : End) (expected : Lists.Error) : Bool :=
  match resolve (commands ending), runModule (commands ending) (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime error) final) =>
    let initial := enter resolved.source caller
    let get (name : String) : Option Lists.Contents := match initial.slots (globalSlot name) with
      | some (.owned address) => final.heap[address]?.map Cell.contents
      | _ => none
    error == expected && get "again" == some (.binding none) && get "later" == some (.binding none) &&
    get "touched" == some (.binding (some (.scalar (.int 0)))) &&
    (match get "first", get "override" with
     | some (.binding (some (.list saved))), some (.binding (some (.list override))) =>
       final.heap[saved]? == some ⟨.list [.scalar (.int 8)], false⟩ &&
       final.heap[override]? == some ⟨.list [.scalar (.int 4)], false⟩
     | _, _ => false) &&
    final.bindingValue (globalSlot "again") == .ok (.scalar (.int 99)) && final.iterators == [123]
  | _, _ => false

#guard errorControl .operand (.indexRange 1 1)
#guard errorControl .surplus (.arity 3 4)
#guard errorControl .missing (.missingArguments ["required"])

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults
