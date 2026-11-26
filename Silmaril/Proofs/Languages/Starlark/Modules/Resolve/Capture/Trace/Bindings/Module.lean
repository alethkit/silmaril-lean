module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Steps

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings

open Silmaril.Languages.Starlark.Modules (enter Catalog)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings
open Silmaril.Languages.Starlark.Functions (Program)
open Silmaril.Languages.Starlark.Lists (State)

private theorem advance {globals : List String} {before rest : List Command} {head : Command}
    {linked : Program} {resolved : ResolvedModule} {state : State} {entries : Environment}
    (declared : ModuleBinders (before ++ head :: rest) globals)
    (checked : resolve (before ++ head :: rest) linked = .ok resolved)
    (step : ∃ out, Leaf.Step resolved globals before.length state head out ∧
      (∀ next, out = .ok () next →
        ModuleSlots globals next ∧ LiveBindings globals resolved.program entries next))
    (remaining : ∀ (earlier : List Command),
      ModuleBinders (earlier ++ rest) globals → resolve (earlier ++ rest) linked = .ok resolved →
      ∀ next, ModuleSlots globals next → LiveBindings globals resolved.program entries next →
        ∃ out, Wrapper.ReachedPrefix (Leaf.Step resolved globals) earlier.length next rest out) :
    ∃ out, Wrapper.ReachedPrefix (Leaf.Step resolved globals) before.length state (head :: rest) out := by
  obtain ⟨out, first, preserved⟩ := step
  cases out with
  | error error final => exact ⟨_, .error first⟩
  | ok _ next =>
    obtain ⟨valid, live⟩ := preserved next rfl
    have decl : ModuleBinders ((before ++ [head]) ++ rest) globals := by
      simpa only [List.append_assoc, List.singleton_append] using declared
    have accept : resolve ((before ++ [head]) ++ rest) linked = .ok resolved := by
      simpa only [List.append_assoc, List.singleton_append] using checked
    obtain ⟨out, tail⟩ := remaining (before ++ [head]) decl accept next valid live
    exact ⟨out, .next first (by simpa only [List.length_append, List.length_singleton] using tail)⟩

private theorem schedule_trace {globals : List String} {entries : Environment} {commands : List Command}
    (profile : Bindings.Schedule globals entries commands)
    (globalsLegal : ∀ name ∈ globals, name.toList.head? ≠ some '$')
    (before : List Command) {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ commands) globals)
    (checked : resolve (before ++ commands) linked = .ok resolved)
    (state : State) (layout : ModuleSlots globals state)
    (pool : LiveBindings globals resolved.program entries state) :
    ∃ out, Wrapper.ReachedPrefix (Leaf.Step resolved globals) before.length state commands out := by
  induction profile generalizing before state with
  | nil => exact ⟨_, .nil⟩
  | define known body tail ih =>
    have suffix := (schedule_static tail).2.1
    obtain ⟨next, first, valid, live⟩ := define_step declared checked body suffix globalsLegal known layout pool
    exact advance declared checked ⟨_, first, by intro _ same; cases same; exact ⟨valid, live⟩⟩ ih
  | setup known allowed tail ih =>
    obtain ⟨out, first, progress⟩ := setup_step declared checked allowed state
    apply advance declared checked ⟨out, first, ?_⟩ ih
    intro next success
    obtain ⟨value, middle, rfl, added⟩ := progress next success
    have preserves : Preserves state middle := by
      rcases added with rfl | ⟨cell, rfl⟩
      · exact Preserves.refl _
      · exact Preserves.push state cell
    exact update_live layout pool preserves (by intro _ impossible; cases impossible)
  | copy src dst tracked tail ih =>
    obtain ⟨next, first, valid, live⟩ := alias_step declared checked src dst tracked layout pool
    exact advance declared checked ⟨_, first, by intro _ same; cases same; exact ⟨valid, live⟩⟩ ih
  | wrapper callee target tracked args tail ih =>
    exact advance declared checked (invoke_step declared checked callee target args tracked layout pool) ih
  | leaf callee target tracked args tail ih =>
    exact advance declared checked (invoke_step declared checked callee target args tracked layout pool) ih

theorem checked_trace {commands : List Command} (profile : Bindings.Profile commands)
    {linked : Program} {resolved : ResolvedModule} (checked : resolve commands linked = .ok resolved)
    (caller : State) :
    ModuleBinders commands (names commands) ∧
      ∃ out, Wrapper.ReachedPrefix (Leaf.Step resolved (names commands)) 0 (enter resolved.source caller) commands out := by
  obtain ⟨declared, _, legal⟩ := schedule_static profile
  exact ⟨declared, schedule_trace profile legal [] declared checked (enter resolved.source caller)
    (entered_slots declared checked caller) (by intro _ _ impossible; cases impossible)⟩

theorem checked_module {commands : List Command} (profile : Bindings.Profile commands)
    {linked : Program} {resolved : ResolvedModule} (checked : resolve commands linked = .ok resolved)
    (host : Catalog) (caller : State) :
    ∃ out published,
      Wrapper.ReachedPrefix (Leaf.Step resolved (names commands)) 0 (enter resolved.source caller) commands out ∧
      Leaf.Finishes (names commands) caller out published ∧
      Initializes commands host caller linked (.ok published) ∧ runModule commands host caller linked = .ok published := by
  obtain ⟨declared, out, reached⟩ := checked_trace profile checked caller
  obtain ⟨observed, finishes⟩ := publication_total _ caller out
  exact ⟨out, observed, reached, finishes, Leaf.checked_module declared checked host caller reached finishes⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings
