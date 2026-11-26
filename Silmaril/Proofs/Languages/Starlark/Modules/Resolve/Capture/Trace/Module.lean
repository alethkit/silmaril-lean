module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Steps

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace

open Silmaril.Languages.Starlark.Modules (globalSlot enter Catalog Published)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Capture Outcome Cell)

local notation "MResult" => Silmaril.Languages.Starlark.Modules.Result

private theorem tail_trace {globals : List String} {commands : List Command} (profile : Tail globals commands)
    (before : List Command) {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ commands) globals)
    (checked : resolve (before ++ commands) linked = .ok resolved) (state : State) :
    ∃ out, Wrapper.ReachedPrefix (Leaf.Step resolved globals) before.length state commands out := by
  induction profile generalizing before state with
  | nil => exact ⟨_, .nil⟩
  | @assign name source rest _ allowed _ ih =>
    obtain ⟨out, step, _⟩ := setup_step declared checked allowed state
    cases out with
    | error error final => exact ⟨_, .error step⟩
    | ok _ next =>
      have declared' : ModuleBinders ((before ++ [.assign name source]) ++ rest) globals := by
        simpa only [List.append_assoc, List.singleton_append] using declared
      have checked' : resolve ((before ++ [.assign name source]) ++ rest) linked = .ok resolved := by
        simpa only [List.append_assoc, List.singleton_append] using checked
      obtain ⟨out, continued⟩ := ih (before ++ [.assign name source]) declared' checked' next
      exact ⟨out, .next step (by simpa only [List.length_append, List.length_singleton] using continued)⟩

private theorem head_found {seed program : Program} {frame : Frame} {rest : List Frame}
    (keeps : Wrapper.KeepsTable seed program (frame :: rest)) :
    program[(EmittedProgram seed rest).size]? = some frame.declaration :=
  keeps _ _ (by simp [EmittedProgram])

private theorem tail_kept {seed program : Program} {frame : Frame} {rest : List Frame}
    (keeps : Wrapper.KeepsTable seed program (frame :: rest)) : Wrapper.KeepsTable seed program rest := by
  intro index declaration found
  have within := (Array.getElem?_eq_some_iff.mp found).choose
  exact keeps _ _ (by simp [EmittedProgram, Array.getElem?_push, Nat.ne_of_lt within, found])

private theorem schedule_trace {globals : List String} {callee : String} {chain : Chain} {commands : List Command}
    (schedule : Schedule globals callee chain commands)
    (before : List Command) {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ commands) globals)
    (checked : resolve (before ++ commands) linked = .ok resolved)
    (state : State) (layout : ModuleSlots globals state) (calleeKnown : Visible globals callee)
    (seed : Program) (frame : Frame) (rest : List Frame) (outer : List (List String)) (enclosing : List String)
    (scopeNames : ∀ name, name ∈ outer.flatten ↔ name ∈ enclosing)
    (definitions : Definitions globals enclosing chain)
    (emits : Emits globals outer chain (frame :: rest)) (links : Links seed chain (frame :: rest))
    (scopes : ScopedLeaves globals outer chain (frame :: rest))
    (keeps : Wrapper.KeepsTable seed resolved.program (frame :: rest))
    (address : Nat) (captures : List Capture)
    (live : RootCall.Live state callee address (EmittedProgram seed rest).size captures false)
    (environment : ∃ owner, Installs owner frame.free captures)
    (legal : ∀ entry ∈ captures, entry.binding.name.toList.head? ≠ some '$') :
    ∃ out, Wrapper.ReachedPrefix (Leaf.Step resolved globals) before.length state commands out := by
  induction schedule generalizing before state frame rest outer enclosing address captures with
  | @setup chain name callee source suffix known unrelated allowed continuing ih =>
    obtain ⟨out, first, result⟩ := setup_step declared checked allowed state
    cases out with
    | error error final => exact ⟨_, .error first⟩
    | ok _ next =>
      obtain ⟨value, staged, rfl, extension⟩ := result _ rfl
      have preserved : ModuleSlots globals staged ∧
          RootCall.Live staged callee address (EmittedProgram seed rest).size captures false := by
        rcases extension with rfl | ⟨cell, rfl⟩
        · exact ⟨layout, live⟩
        · exact ⟨push_keeps layout cell, push_live live layout calleeKnown.1 cell⟩
      have kept := (RootCall.write_keeps_live staged callee name value preserved.1.distinct
        preserved.2 unrelated).2
      have declared' : ModuleBinders ((before ++ [.assign name source]) ++ suffix) globals := by
        simpa only [List.append_assoc, List.singleton_append] using declared
      have checked' : resolve ((before ++ [.assign name source]) ++ suffix) linked = .ok resolved := by
        simpa only [List.append_assoc, List.singleton_append] using checked
      obtain ⟨out, tail⟩ := ih (before ++ [.assign name source]) declared' checked' _
        (written_slots preserved.1 _ _) calleeKnown _ _ _ _ scopeNames definitions emits links scopes keeps _ _ kept
        environment legal
      exact ⟨out, .next first (by simpa only [List.length_append, List.length_singleton] using tail)⟩
  | @wrapper name callee parameters child destination arguments commands known allowed continuing ih =>
    cases definitions with
    | wrapper paramsLegal childLegal childSyntax =>
      cases links with
      | @wrapper _ _ _ _ childFrame frames childOwned wrapperCode childLinks =>
        cases emits with
        | @wrapper _ _ _ locals _ _ _ _ _ collect childEmits _ =>
          cases scopes with
          | wrapper childScopes =>
            have scopesEq := child_scopes (outer := outer) collect scopeNames
            have layoutLegal := singleton_legal collect paramsLegal childLegal
            let canContinue (stored : State) : Prop :=
              ModuleSlots globals stored ∧
                ∃ address selected, RootCall.Live stored destination address (EmittedProgram seed frames).size
                  selected false ∧ (∃ owner, Installs owner childFrame.free selected) ∧
                  (∀ entry ∈ selected, entry.binding.name.toList.head? ≠ some '$')
            obtain ⟨out, first, progress⟩ := call_step declared checked calleeKnown allowed live (head_found keeps)
              canContinue (fun assigned => by
                obtain ⟨out, ran, result⟩ := child_total (name := name) (.wrapper collect childEmits (by assumption))
                  (.wrapper childOwned wrapperCode childLinks) keeps state layout known.1 captures environment legal
                  layoutLegal assigned
                refine ⟨out, ran, fun value next done => ?_⟩
                obtain ⟨valid, _, live⟩ := result value next done
                exact ⟨valid, live⟩)
            cases out with
            | error error final => exact ⟨_, .error first⟩
            | ok _ next =>
              obtain ⟨nextLayout, nextAddress, selected, nextLive, nextEnvironment, selectedLegal⟩ := progress _ rfl
              have declared' : ModuleBinders ((before ++ [invocation callee destination arguments]) ++ commands) globals := by
                simpa only [List.append_assoc, List.singleton_append] using declared
              have checked' : resolve ((before ++ [invocation callee destination arguments]) ++ commands) linked =
                  .ok resolved := by
                simpa only [List.append_assoc, List.singleton_append] using checked
              obtain ⟨out, tail⟩ := ih (before ++ [invocation callee destination arguments]) declared' checked' next
                nextLayout known childFrame frames _ _ scopesEq childSyntax childEmits childLinks childScopes
                (tail_kept keeps) nextAddress selected nextLive nextEnvironment selectedLegal
              exact ⟨out, .next first (by simpa only [List.length_append, List.length_singleton] using tail)⟩
  | @leaf name callee parameters body destination arguments commands known allowed suffix =>
    obtain ⟨plan, lexical, planLegal, ownedLegal⟩ := leaf_plan definitions scopeNames emits
    cases scopes with
    | mixed leaf =>
      obtain ⟨out, first, _⟩ := call_step declared checked calleeKnown allowed live (head_found keeps) (fun _ => True)
        (fun assigned => by
          obtain ⟨out, ran⟩ := leaf_total plan (activate state frame.declaration captures assigned)
          exact ⟨_, .leaf leaf lexical planLegal ownedLegal legal ran, by intros; trivial⟩)
      cases out with
      | error error final => exact ⟨_, .error first⟩
      | ok _ next =>
        have declared' : ModuleBinders ((before ++ [invocation callee destination arguments]) ++ commands) globals := by
          simpa only [List.append_assoc, List.singleton_append] using declared
        have checked' : resolve ((before ++ [invocation callee destination arguments]) ++ commands) linked =
            .ok resolved := by
          simpa only [List.append_assoc, List.singleton_append] using checked
        obtain ⟨out, tail⟩ := tail_trace suffix (before ++ [invocation callee destination arguments]) declared' checked' next
        exact ⟨out, .next first (by simpa only [List.length_append, List.length_singleton] using tail)⟩

theorem checked_trace {chain : Chain} {after : List Command} (profile : Profile chain after)
    {linked : Program} {resolved : ResolvedModule} (checked : resolve (root chain :: after) linked = .ok resolved)
    (caller : State) :
    let commands := root chain :: after
    let globals := names commands
    ModuleBinders commands globals ∧
      ∃ out, Wrapper.ReachedPrefix (Leaf.Step resolved globals) 0 (enter resolved.source caller) commands out := by
  let globals := names (root chain :: after)
  have ⟨afterBinders, segment⟩ := schedule_binders profile.schedule
  have declared : ModuleBinders (root chain :: after) globals :=
    .cons (.define _ _ _) afterBinders
  refine ⟨declared, ?_⟩
  have accepted (program : Program) : Accepted globals program [] chain :=
    definitions_accept profile.definitions program [] (fun _ => Iff.rfl)
  obtain ⟨seed, frame, rest, emits, links, scopes, site, keeps⟩ :=
    RootCall.checked_chain_scoped_site after chain globals linked resolved declared checked accepted segment
  let id := (EmittedProgram seed rest).size
  let initial := enter resolved.source caller
  have found := head_found keeps
  have initialLayout := entered_slots declared checked caller
  have known : Visible globals chain.name := ⟨by change chain.name ∈ chain.name :: _; simp, profile.rootName⟩
  obtain ⟨captures, installed⟩ : ∃ captures, Installs initial frame.free captures := by
    apply installs_of_addresses
    intro entry present
    obtain ⟨name, member, description⟩ := root_capture emits entry present
    obtain ⟨address, _, _, owned, _⟩ := initialLayout.usable name member
    exact ⟨globalSlot name, address, description, .inl owned⟩
  let added : Cell := ⟨.function ⟨id, captures, []⟩, false⟩
  let grown : State := { initial with heap := initial.heap.push added }
  let made := grown.write (globalSlot chain.name) (.function initial.heap.size)
  have first : Leaf.Step resolved globals 0 initial (root chain) (.ok () made) := .define site found installed
  have grownLayout : ModuleSlots globals grown := push_keeps initialLayout added
  obtain ⟨slot, _, _, owned, stored⟩ := grownLayout.usable _ known.1
  have layout := written_slots grownLayout (globalSlot chain.name) (.function initial.heap.size)
  have live : RootCall.Live made chain.name initial.heap.size id captures false := by
    refine ⟨⟨slot, ?_⟩, writes_binding _ _ _ _ owned stored, write_keeps_function _ _ _ _ _ _ ?_⟩
    · simpa only [made, slots_write] using owned
    · change (initial.heap.push added)[initial.heap.size]? = _
      simp [added]
  have legal : ∀ entry ∈ captures, entry.binding.name.toList.head? ≠ some '$' := by
    apply captures_from_declared installed
    intro entry present
    obtain ⟨name, member, rfl⟩ := root_capture emits entry present
    rcases List.mem_cons.mp member with rfl | later
    · exact profile.rootName
    · exact schedule_legal profile.schedule _ later
  obtain ⟨out, tail⟩ := schedule_trace profile.schedule [root chain] declared checked made layout known seed frame rest
    [] [] (fun _ => Iff.rfl) profile.definitions emits links scopes keeps initial.heap.size captures live
    ⟨initial, installed⟩ legal
  exact ⟨out, .next first tail⟩

theorem checked_source_module {chain : Chain} {after : List Command} (profile : Profile chain after)
    {linked : Program} {resolved : ResolvedModule} (checked : resolve (root chain :: after) linked = .ok resolved)
    (host : Catalog) (caller : State) :
    let commands := root chain :: after
    let globals := names commands
    ∃ out published,
      Wrapper.ReachedPrefix (Leaf.Step resolved globals) 0 (enter resolved.source caller) commands out ∧
      Leaf.Finishes globals caller out published ∧
      Initializes commands host caller linked (.ok published) ∧ runModule commands host caller linked = .ok published := by
  obtain ⟨declared, out, reached⟩ := checked_trace profile checked caller
  obtain ⟨observed, finishes⟩ := publication_total _ caller out
  exact ⟨out, observed, reached, finishes, Leaf.checked_module declared checked host caller reached finishes⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace
