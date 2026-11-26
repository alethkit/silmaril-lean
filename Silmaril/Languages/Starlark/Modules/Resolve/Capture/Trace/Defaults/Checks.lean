module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults

open scoped Functions.Lowering.Quote
open Lists (Cell State)

private def pick : Definition :=
  ⟨"pick", ⟨["seed"], [("x", starlark%[seed]), ("buf", starlark%[[1]])]⟩, "x"⟩

private def setup : List Command := [.assign "seed" starlark%[[3]]]
private def copy : List Command := [.assign "saved" starlark%[pick]]

private theorem admitted : ModuleProfile setup copy pick := by
  refine ⟨.assign (by unfold Visible; decide) (.list ?_) .nil, .assign (by unfold Visible; decide) (.operand (.read (by unfold Visible; decide))) .nil, ?_⟩
  · intro operand member
    simp at member
    subst operand
    exact .int 3
  · refine ⟨?_, by unfold Visible; decide⟩
    intro default member
    simp only [pick, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .operand (.read (by unfold Visible; decide))
    · apply Initializer.list
      intro operand present
      simp at present
      subst operand
      exact .int 1

example {resolved : ResolvedModule} (checked : resolve (setup ++ pick.command :: copy) = .ok resolved) :
    ∃ out observation,
      Wrapper.ReachedPrefix (Step resolved (names (setup ++ pick.command :: copy))) 0
        (enter resolved.source {}) (setup ++ pick.command :: copy) out ∧
      Leaf.Finishes (names (setup ++ pick.command :: copy)) {} out observation ∧
      Initializes (setup ++ pick.command :: copy) (fun _ => none) {} #[] (.ok observation) ∧
      runModule (setup ++ pick.command :: copy) (fun _ => none) {} = .ok observation :=
  checked_module admitted checked (fun _ => none) {}

-- The second saved default is only reachable through the exported closure.
#guard
  match runModule (setup ++ pick.command :: copy) (fun _ => none) {} with
  | .ok (.ok published final) =>
    match published.exports.lookup "seed", published.exports.lookup "pick" with
    | some (.list seed), some (.function function) =>
      published.exports.map Prod.fst == ["seed", "pick", "saved"] &&
      published.exports.lookup "saved" == some (.function function) &&
      (match final.heap[function]? with
       | some ⟨.function closure, true⟩ =>
         match closure.defaults with
         | [(x, .list savedSeed), (buf, .list savedBuffer)] =>
           x == fileSlot "x" && buf == fileSlot "buf" && savedSeed == seed &&
           final.heap[savedSeed]? == some ⟨.list [.scalar (.int 3)], true⟩ &&
           final.heap[savedBuffer]? == some ⟨.list [.scalar (.int 1)], true⟩
         | _ => false
       | _ => false)
    | _, _ => false
  | _ => false

private def broken : Definition :=
  ⟨"broken", ⟨[], [("a", starlark%[[1]]), ("b", starlark%[later]), ("c", starlark%[[3]])]⟩, "a"⟩

private def later : List Command := [.assign "later" starlark%[5]]

private theorem failureAdmitted : ModuleProfile [] later broken := by
  refine ⟨.nil, .assign (by unfold Visible; decide) (.operand (.int 5)) .nil, ⟨?_, by unfold Visible; decide⟩⟩
  intro default member
  simp only [broken, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .list (by intro operand present; simp at present; subst operand; exact .int 1)
  · exact .operand (.read (by unfold Visible; decide))
  · exact .list (by intro operand present; simp at present; subst operand; exact .int 3)

example {resolved : ResolvedModule} (checked : resolve (broken.command :: later) = .ok resolved) :
    ∃ out observation,
      Wrapper.ReachedPrefix (Step resolved (names (broken.command :: later))) 0
        (enter resolved.source {}) (broken.command :: later) out ∧
      Leaf.Finishes (names (broken.command :: later)) {} out observation ∧
      Initializes (broken.command :: later) (fun _ => none) {} #[] (.ok observation) ∧
      runModule (broken.command :: later) (fun _ => none) {} = .ok observation :=
  checked_module failureAdmitted checked (fun _ => none) {}

private def caller : State := {
  bindings := fun _ => some (.scalar (.int 99))
  iterators := [123]
}

-- No installation or publication occurs. Only the first default allocated.
#guard
  match runModule (broken.command :: later) (fun _ => none) caller with
  | .ok (.error (.runtime (.uninitialized binding)) final) =>
    binding == globalSlot "later" &&
    final.heap.toList == [⟨.binding none, false⟩, ⟨.binding none, false⟩, ⟨.list [.scalar (.int 1)], false⟩] &&
    final.bindingValue (globalSlot "broken") == .ok (.scalar (.int 99)) && final.iterators == [123]
  | _ => false

-- The native module evaluator also supports calls and mutation. These
-- controls exercise saved aliasing beyond the source sequencing theorem.
private def callPrefix : List Command := setup ++ [pick.command] ++ copy ++
  [.setIndex starlark%[seed] starlark%[0] starlark%[8]]

#guard
  match runModule (callPrefix ++ [.assign "omitted" starlark%[saved(0)],
      .assign "override" starlark%[saved(0, [4])], .assign "again" starlark%[saved(0)]]) (fun _ => none) {} with
  | .ok (.ok published final) =>
    match published.exports.lookup "seed", published.exports.lookup "override" with
    | some (.list seed), some (.list overridden) =>
      published.exports.lookup "omitted" == some (.list seed) &&
      published.exports.lookup "again" == some (.list seed) &&
      final.heap[seed]? == some ⟨.list [.scalar (.int 8)], true⟩ &&
      final.heap[overridden]? == some ⟨.list [.scalar (.int 4)], true⟩ &&
      (final.heap.filter (fun cell => cell.contents == .list [.scalar (.int 1)])).size == 1
    | _, _ => false
  | _ => false

#guard
  match runModule (callPrefix ++ [.assign "result" starlark%[saved()]]) (fun _ => none) {} with
  | .ok (.error (.runtime (.missingArguments ["seed"])) _) => true
  | _ => false

#guard
  match runModule (callPrefix ++ [.assign "result" starlark%[saved(0, 1, 2, 3)]]) (fun _ => none) {} with
  | .ok (.error (.runtime (.arity 3 4)) _) => true
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
