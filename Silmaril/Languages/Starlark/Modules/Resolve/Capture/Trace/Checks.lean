module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace

open scoped Functions.Lowering.Quote
open Block (ModuleBinders)
open Lists (State Cell)

local notation "Expr" => Functions.Lowering.Resolve.SourceExpr

private def chain : Forwarding.Chain :=
  .wrapper "outer" ["box"] (.wrapper "bridge" [] (.mixed "leaf" ["idx"]
    ⟨"idx", starlark%[box], starlark%[idx], .plain starlark%[_pair], starlark%[later]⟩))

private def rootCommand : Command := .define chain.name (.required chain.parameters) chain.body

private def call (callee destination : String) (arguments : List Expr) : Command :=
  .assign destination (.call (.scalar (.read callee)) arguments [] none none)

private def observation (arguments : List Expr) : Command := call "saved" "out" arguments
private def initializeLater : Command := .assign "later" starlark%[9]

private def suffix (initialized : Bool) (actuals : List Expr) : List Command :=
  [.assign "box" starlark%[[3]],
    call "outer" "bridge_saved" [starlark%[box]],
    .assign "_pair" starlark%[(0, 9)],
    call "bridge_saved" "saved" []] ++
  if initialized then [initializeLater, observation actuals] else [observation actuals, initializeLater]

private def ordinary : List Expr := [starlark%[1]]
private def earlyFailure : List Expr := [starlark%[_pair[2]], starlark%[1]]

private theorem admitted (initialized : Bool) (actuals : List Expr)
    (known : ∀ item ∈ actuals, Operand (names (root chain :: suffix initialized actuals)) item) :
    Profile chain (suffix initialized actuals) := by
  have visible (name : String) (member : name ∈ ["box", "bridge_saved", "_pair", "saved", "later", "out"]) :
      Visible (names (root chain :: suffix initialized actuals)) name := by
    cases initialized <;> simp [Visible, names, root, suffix, call, observation, initializeLater,
      chain, Forwarding.Chain.name] at * <;>
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨by decide, .wrapper (by intro name member; simp at member; subst name; decide) (by decide)
    (.wrapper (by simp) (by decide)
      (.mixed (by intro name member; simp at member; subst name; decide) (by decide)
        ?_ ?_ ?_ ?_)), ?_⟩
  all_goals try
    solve
    | cases initialized <;> simp [Visible, names, root, suffix, call, observation,
        initializeLater, chain, Forwarding.Chain.name]
  · refine .setup (visible "box" (by decide)) (by decide) (.list ?_) (.wrapper
      (visible "bridge_saved" (by decide)) ?_ (.setup (visible "_pair" (by decide)) (by decide)
        (.tuple ?_) (.wrapper (visible "saved" (by decide)) (by simp) ?_)))
    · intro item member
      simp at member
      subst item
      exact .int 3
    · intro item member
      simp at member
      subst item
      exact .read (visible "box" (by decide))
    · intro item member
      simp at member
      rcases member with rfl | rfl
      · exact .int 0
      · exact .int 9
    · cases initialized with
      | false =>
        exact .leaf (visible "out" (by decide)) known
          (.assign (visible "later" (by decide)) (.operand (.int 9)) .nil)
      | true =>
        exact .setup (visible "later" (by decide)) (by decide) (.operand (.int 9))
          (.leaf (visible "out" (by decide)) known .nil)

private theorem ordinary_profile (mode : Bool) : Profile chain (suffix mode ordinary) :=
  admitted mode ordinary (by
    intro item member
    simp [ordinary] at member
    subst item
    exact .int 1)

private theorem operand_error_profile : Profile chain (suffix true earlyFailure) :=
  admitted true earlyFailure (by
    intro item member
    simp [earlyFailure] at member
    rcases member with rfl | rfl
    · exact .index (.read (by simp [Visible, names, root, suffix, call, observation,
        initializeLater, chain, Forwarding.Chain.name])) (.int 2)
    · exact .int 1)

-- Both command orders get the source trace and exact module observation
-- from the theorem. The only proof inputs are syntax and checked intake.
example (mode : Bool) {resolved : ResolvedModule}
    (checked : resolve (root chain :: suffix mode ordinary) = .ok resolved) :
    ∃ out observed,
      Wrapper.ReachedPrefix (Leaf.Step resolved (names (root chain :: suffix mode ordinary))) 0
        (enter resolved.source {}) (root chain :: suffix mode ordinary) out ∧
      Leaf.Finishes (names (root chain :: suffix mode ordinary)) {} out observed ∧
      Initializes (root chain :: suffix mode ordinary) (fun _ => none) {} #[] (.ok observed) ∧
      runModule (root chain :: suffix mode ordinary) (fun _ => none) {} = .ok observed :=
  checked_source_module (ordinary_profile mode) checked (fun _ => none) {}

example {resolved : ResolvedModule}
    (checked : resolve (root chain :: suffix true earlyFailure) = .ok resolved) :
    ModuleBinders (root chain :: suffix true earlyFailure) (names (root chain :: suffix true earlyFailure)) ∧
      ∃ out, Wrapper.ReachedPrefix (Leaf.Step resolved (names (root chain :: suffix true earlyFailure))) 0
        (enter resolved.source {}) (root chain :: suffix true earlyFailure) out :=
  checked_trace operand_error_profile checked {}

private def caller : State := {
  bindings := fun _ => some (.scalar (.int 17))
  iterators := [42]
}

#guard
  match runModule (rootCommand :: suffix true ordinary) (fun _ => none) caller with
  | .ok (.ok published final) =>
    published.exports.map Prod.fst == ["outer", "box", "bridge_saved", "saved", "later", "out"] &&
      published.exports.lookup "out" == some (.scalar (.int 9)) &&
      (match published.exports.lookup "box" with
      | some (.list address) => final.heap[address]? == some ⟨.list [.scalar (.int 9)], true⟩
      | _ => false) &&
      final.heap.any (fun cell => match cell.contents with
        | .tuple _ _ => cell.frozen
        | _ => false) &&
      final.iterators == [42]
  | _ => false

#guard
  let commands := rootCommand :: suffix false ordinary
  match resolve commands, runModule commands (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime (.uninitialized missing)) final) =>
    let initial := enter resolved.source caller
    let unset := fun name => match initial.slots (globalSlot name) with
      | some (.owned address) => final.heap[address]? == some ⟨.binding none, false⟩
      | _ => false
    missing == globalSlot "later" && unset "out" && unset "later" &&
      final.heap.any (fun cell => cell == ⟨.list [.scalar (.int 9)], false⟩) &&
      final.bindingValue (globalSlot "out") == .ok (.scalar (.int 17)) && final.iterators == [42]
  | _, _ => false

-- A reached argument error wins over surplus arguments and skips the leaf.
#guard
  match runModule (rootCommand :: suffix true earlyFailure) (fun _ => none) caller with
  | .ok (.error (.runtime (.indexRange 2 2)) final) =>
    final.heap.any (fun cell => cell == ⟨.list [.scalar (.int 3)], false⟩) && final.iterators == [42]
  | _ => false

-- With no operand error, the missing argument skips the leaf as well.
#guard
  match runModule (rootCommand :: suffix true []) (fun _ => none) caller with
  | .ok (.error (.runtime (.missingArguments ["idx"])) final) =>
    final.heap.any (fun cell => cell == ⟨.list [.scalar (.int 3)], false⟩) && final.iterators == [42]
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
