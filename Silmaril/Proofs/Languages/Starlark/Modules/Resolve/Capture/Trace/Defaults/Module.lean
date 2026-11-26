module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Site

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults

open Silmaril.Languages.Starlark.Modules (enter Catalog Executes Published finish fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome)

local notation "Result" => Silmaril.Languages.Starlark.Modules.Result

theorem step_sound {globals : List String} {resolved : ResolvedModule}
    {index : Nat} {state : State} {command : Command} {out : Result Unit}
    (step : Defaults.Step resolved globals index state command out) (host : Catalog) :
    ∃ code, resolved.source.commands[index]? = some code ∧ Executes resolved.program host state code out := by
  cases step with
  | setup site evaluated =>
    have ran := ExecExpr.evaluates (fun _ _ _ impossible => impossible.elim)
      (setup_eval resolved.program (List.range resolved.program.size) evaluated)
    cases ‹Outcome Silmaril.Languages.Starlark.Lists.Value› <;>
      exact ⟨_, site, .exec (code := .assignExpr _ _) (.assignExpr ran)⟩
  | define site found length evaluated =>
    exact ⟨_, site, .exec (code := .define _ _)
      (definition_sound _ _ _ _ _ _ _ found (default_slots _ _) length evaluated).1⟩

private theorem setup_binders {globals : List String} {commands : List Command} (source : Tail globals commands) :
    ModuleBinders commands (names commands) ∧ RootCall.Segment globals commands := by
  induction source with
  | nil => exact ⟨.nil, .nil⟩
  | assign _ _ _ ih => exact ⟨.cons (.assign _ _) ih.1, .assign _ _ ih.2⟩

private theorem attach_binders {before after : List Command} {left right : List String}
    (prefixBinders : ModuleBinders before left)
    (suffixBinders : ModuleBinders after right) :
    ModuleBinders (before ++ after) (left ++ right) := by
  induction prefixBinders with
  | nil => exact suffixBinders
  | cons first rest ih =>
    rw [List.cons_append, List.append_assoc]
    exact .cons first ih

private theorem names_append (before after : List Command) :
    names (before ++ after) = names before ++ names after := by
  induction before with
  | nil => rfl
  | cons first rest ih => cases first <;> simp [names, ih]

private theorem setup_trace {globals : List String} {setup : List Command}
    (source : Tail globals setup) (earlier suffix : List Command) {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (earlier ++ setup ++ suffix) globals)
    (checked : resolve (earlier ++ setup ++ suffix) linked = .ok resolved) (state : State)
    (remaining : ∀ next, ∃ out,
      Wrapper.ReachedPrefix (Defaults.Step resolved globals) (earlier.length + setup.length) next suffix out) :
    ∃ out, Wrapper.ReachedPrefix (Defaults.Step resolved globals) earlier.length state (setup ++ suffix) out := by
  induction source generalizing earlier state with
  | nil => simpa using remaining state
  | @assign name source setup known admitted tail ih =>
    obtain ⟨code, reads, out, tracked, evaluated, _⟩ := setup_value admitted state
    have position : ModuleBinders (earlier ++ .assign name source :: (setup ++ suffix)) globals := by
      simpa only [List.cons_append, List.append_assoc] using declared
    have verified : resolve (earlier ++ .assign name source :: (setup ++ suffix)) linked = .ok resolved := by
      simpa only [List.cons_append, List.append_assoc] using checked
    have site := RootCall.checked_assign_site earlier (setup ++ suffix) name source code reads globals linked resolved
      position verified tracked
    have first := Defaults.Step.setup site evaluated
    cases out with
    | error error next => exact ⟨_, .error first⟩
    | ok value next =>
      have decl' : ModuleBinders ((earlier ++ [.assign name source]) ++ setup ++ suffix) globals := by
        simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using declared
      have check' : resolve ((earlier ++ [.assign name source]) ++ setup ++ suffix) linked = .ok resolved := by
        simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using checked
      obtain ⟨out, rest⟩ := ih (earlier ++ [.assign name source]) decl' check' _
        (fun final => by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using remaining final)
      exact ⟨out, .next (rest := setup ++ suffix) first (by
        simpa only [List.length_append, List.length_singleton] using rest)⟩

theorem checked_module {before after : List Command} {definition : Definition}
    (profile : ModuleProfile before after definition) {linked : Program} {resolved : ResolvedModule}
    (checked : resolve (before ++ definition.command :: after) linked = .ok resolved)
    (host : Catalog) (caller : State) :
    let commands := before ++ definition.command :: after
    let globals := names commands
    ∃ out published,
      Wrapper.ReachedPrefix (Defaults.Step resolved globals) 0 (enter resolved.source caller) commands out ∧
      Leaf.Finishes globals caller out published ∧
      Initializes commands host caller linked (.ok published) ∧ runModule commands host caller linked = .ok published := by
  let globals := names (before ++ definition.command :: after)
  have ⟨left, _⟩ := setup_binders profile.beforeSetup
  have ⟨right, segment⟩ := setup_binders profile.afterSetup
  have commandBinders : ModuleBinders (definition.command :: after) (names (definition.command :: after)) :=
    .cons (.define _ _ _) right
  have declared : ModuleBinders (before ++ definition.command :: after) globals := by
    simpa only [globals, names_append] using attach_binders left commandBinders
  obtain ⟨id, codes, site, found, length, evaluation⟩ :=
    checked_definition_site declared checked profile.definitionAllowed segment
  have continueDefinition (state : State) :
      ∃ out, Wrapper.ReachedPrefix (Defaults.Step resolved globals) before.length state (definition.command :: after) out := by
    obtain ⟨out, ran⟩ := evaluation state
    cases out with
    | error error residual =>
      exact ⟨_, .error (.define site found length (.failed ran))⟩
    | ok values residual =>
      let next := install (Silmaril.Languages.Starlark.Modules.globalSlot definition.name) id []
        ((definition.parameters.optional.map (fileSlot ∘ Prod.fst)).zip values) residual
      have first : Defaults.Step resolved globals before.length state definition.command (.ok () next) :=
        .define site found length (.installed ran .nil)
      let earlier := before ++ [definition.command]
      have same : earlier ++ after ++ [] = before ++ definition.command :: after := by
        simp [earlier, List.append_assoc]
      have declared' : ModuleBinders (earlier ++ after ++ []) globals := by simpa only [same] using declared
      have checked' : resolve (earlier ++ after ++ []) linked = .ok resolved := by simpa only [same] using checked
      obtain ⟨out, rest⟩ := setup_trace (globals := globals) profile.afterSetup earlier [] declared' checked' next
        (fun _ => ⟨_, .nil⟩)
      exact ⟨out, .next first (by simpa [earlier] using rest)⟩
  obtain ⟨out, trace⟩ := setup_trace profile.beforeSetup [] (definition.command :: after) declared checked
    (enter resolved.source caller) (by simpa using continueDefinition)
  obtain ⟨observed, finishes⟩ := publication_total globals caller out
  have finishEq : finish resolved.source caller out = observed :=
    Leaf.finish_agrees (Entry.checked_module_globals declared checked) finishes
  have agreement := Wrapper.checked_finish checked host caller (fun _ _ _ _ step => step_sound step host) trace
  rw [finishEq] at agreement
  exact ⟨out, observed, trace, finishes, agreement⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
