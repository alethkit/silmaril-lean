module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Defs
public import Silmaril.Languages.Starlark.Modules.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Elaboration
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Frame
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Thms
import Silmaril.Languages.Starlark.Modules.Thms
import Silmaril.Languages.Starlark.Lists.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (globalSlot Catalog enter finish Published TopCode)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive
  (lexical_defaults default_layout)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call
  (ClosureAt BodyEntry)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance
  (runs_activated_for entry_guard return_link invoked_value_at)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named (RunsAt runs_at)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome Cell Capture)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

local notation "Value" => Lists.Value
private abbrev Ready (globals : List String) (program : Program) (env : Environment) : Prop :=
  ∀ name callee, env name = some callee → name ∈ globals ∧ callee.Linked program

private theorem ready_update {globals : List String} {program : Program} {env : Environment}
    (ready : Ready globals program env) {name : String} (member : name ∈ globals) (entry : Option Callable)
    (new : ∀ callee, entry = some callee → callee.Linked program) :
    Ready globals program (update env name entry) := by
  intro read callee tracked
  by_cases same : read = name
  · subst read
    exact ⟨member, new callee (by simpa [update] using tracked)⟩
  · exact ready read callee (by simpa [update, same] using tracked)

private theorem known_globals {globals : List String} {program : Program} {env : Environment}
    (ready : Ready globals program env) : ∀ name callee, env name = some callee → name ∈ globals :=
  fun name callee found => (ready name callee found).1

private theorem root_found {globals : List String} {root : Root globals} {program : Program}
    (known : PreservesDeclarations root.table program) : program[root.id]? = some root.site.declaration :=
  known _ _ Array.getElem?_push_size

private theorem root_linked {globals : List String} {root : Root globals} {program : Program}
    (known : PreservesDeclarations root.table program) : root.callable.Linked program := by
  refine ⟨root_found known, root.seed, root.bodyTable, root.children, rfl, ?_, root.suite⟩
  intro id declaration found
  exact known _ _ (by simp [Root.table, Array.getElem?_push, Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp found).choose, found])

private theorem enter_callable {callee : Callable}
    {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (known : callee.Linked resolved.program) :
    BodyEntry callee.site resolved.program (List.range resolved.program.size) callee.id callee.BodyRuns := by
  obtain ⟨_, seed, bodyTable, children, size, table, suite⟩ := known
  have guarded := entry_guard suite table
  rw [size] at guarded
  intro caller defining captures installed live assigned
  obtain ⟨out, ran, _, kept, exec, _, resultRecord⟩ :=
    runs_activated_for callee.site suite checked table _ guarded caller defining captures installed live assigned
  exact ⟨out, ⟨ran, resultRecord⟩, exec, Body.returned_keeps caller callee.site.declaration captures assigned out kept⟩

private theorem returned_linked {callee : Callable} {program : Program} (known : callee.Linked program) :
    ∀ next, callee.returned.map Callable.nested = some next → next.Linked program := by
  intro next found
  cases result : callee.returned with
  | none => simp [result] at found
  | some entry =>
    have same : Callable.nested entry = next := by simpa [result] using found
    subst next
    obtain ⟨_, _, _, _, _, table, suite⟩ := known
    exact return_link suite table (fun _ _ no => nomatch no) entry result

private theorem returned_record {globals : List String} {callee : Callable} {call : Invocation globals}
    {state reached : State} {value : Value}
    (ran : RunsAt callee.site callee.BodyRuns
      (moduleLex globals) callee.id call.callee (globalSlot call.callee)
      call.arguments call.codes call.keywords.source call.keywords.codes call.star call.mapping state (.ok value reached)) :
    ∀ next, callee.returned.map Callable.nested = some next → ∃ address defining, value = .function address ∧
      Nonempty (ClosureAt next.site next.id defining reached address) := by
  intro next found
  cases result : callee.returned with
  | none => simp [result] at found
  | some entry =>
    have same : Callable.nested entry = next := by simpa [result] using found
    subst next
    unfold Callable.BodyRuns at ran
    rw [result] at ran
    exact invoked_value_at ran

private theorem read_global {globals : List String} {name : String} {state : State} {value : Value}
    (member : name ∈ globals) (loaded : state.bindingValue (globalSlot name) = .ok value) :
    Body.Evaluates (moduleLex globals) state (.scalar (.read name)) (Leaf.readOperand (globalSlot name))
      (.ok value state) := by
  have read := Body.Evaluates.read (state := state)
    (Assignment.ReadResolves.global (block := moduleLex globals) (by simp [moduleLex]) (by simp [moduleLex]) member)
  change Body.Evaluates (moduleLex globals) state (.scalar (.read name)) (Leaf.readOperand (globalSlot name))
    (state.read (.bound (globalSlot name))) at read
  rw [State.read, loaded] at read
  exact read

private theorem native_assignment (program : Program) (host : Catalog) (state : State) (name : String)
    (code : Lowering.Expr) (out : Outcome Value)
    (ran : ExecExpr program (List.range program.size) state code out) :
    Modules.Executes program host state (.exec (.assignExpr name code)) (afterWrite name out) := by
  cases out <;> exact .exec (code := .assignExpr name code) (.assignExpr ran)

private theorem copy_record {globals : List String} {env : Environment} {state middle : State}
    {source : Lowering.Resolve.SourceExpr} {code : Lowering.Expr} {entry : Option Callable} {value : Value}
    (tracks : Tracks env source code entry)
    (evaluated : Body.Evaluates (moduleLex globals) state source code (.ok value middle))
    (live : Live env state) :
    ∀ root, entry = some root → ∃ address defining, value = .function address ∧
      Nonempty (ClosureAt root.site root.id defining middle address) := by
  intro reached selected
  cases tracks with
  | forget => cases selected
  | copy lookup =>
    cases selected
    obtain ⟨address, defining, loaded, ⟨record⟩⟩ := live _ _ lookup
    generalize outcome : (EStateM.Result.ok value middle : Outcome Value) = result at evaluated
    cases evaluated with
    | read resolution =>
      rw [State.read, loaded] at outcome
      cases outcome
      exact ⟨address, defining, rfl, ⟨record⟩⟩

private theorem grow (state : State) (cell : Cell) :
    Body.Keeps state.heap.size state {state with heap := state.heap.push cell} := by
  exact ⟨rfl, fun address _ below old => by simp [Array.getElem?_push, Nat.ne_of_lt below, old]⟩

private theorem reached_definition {globals : List String} {env : Environment} {state : State}
    (root : Root globals) (program : Program) (host : Catalog)
    (found : program[root.id]? = some root.site.declaration)
    (frame : Frame globals state) (live : Live env state)
    (tracked : ∀ name root, env name = some root → name ∈ globals) :
    ∃ out, Executes globals state root.command out ∧
      Modules.Executes program host state (.exec (.define root.site.name root.id)) out ∧
      (∀ next, out = .ok () next → Frame globals next ∧ Live (update env root.site.name (some root.callable)) next) := by
  obtain ⟨captures, installed, cells⟩ := root_captures root frame
  have lexical := lexical_defaults root.site root.lexical
  have ⟨keys, codes⟩ := default_layout root.site root.lexical
  obtain ⟨out, source, exec, _, _⟩ := Lexical.defines_for_total program (List.range program.size)
    (globalSlot root.site.name) root.id root.site.declaration lexical found keys codes state captures installed
  refine ⟨Modules.afterCode out, .define root captures installed source, .exec exec, ?_⟩
  intro next success
  cases source with
  | failed => cases success
  | @installed evaluated values liveCaptures defaultRan capturesRan =>
    cases success
    have kept := Lexical.evaluates_keeps lexical defaultRan
    let saved := root.site.defaultKeys.zip values
    let cell : Cell := ⟨.function ⟨root.id, liveCaptures, saved⟩, false⟩
    let grown := {evaluated with heap := evaluated.heap.push cell}
    have retained : Body.Keeps state.heap.size state grown := by
      refine Body.keeps_trans kept ⟨rfl, fun address entry _ old => ?_⟩
      exact (grow evaluated cell).2 address entry (Array.getElem?_eq_some_iff.mp old).choose old
    have grownFrame := keep_frame frame retained
    have sameCaptures : liveCaptures = captures := Except.ok.inj
      ((installs_lookup evaluated capturesRan).symm.trans
        (installs_lookup evaluated (installs_in_same_slots kept.1 installed)))
    subst liveCaptures
    have captureLive := keep_captures cells kept
    let record : ClosureAt root.site root.id evaluated grown evaluated.heap.size :=
      ⟨captures, values, false, Lexical.evaluated_length lexical defaultRan,
        Array.getElem?_push_size, capturesRan, keep_captures captureLive (grow evaluated cell)⟩
    exact ⟨write_frame (.function evaluated.heap.size) grownFrame root.site.target,
      write_live grownFrame (keep_live frame live tracked retained) tracked root.site.target _
        (some root.callable) (fun known equal => by cases equal; exact ⟨_, _, rfl, ⟨record⟩⟩)⟩

private theorem run_plan {globals : List String} {env : Environment} {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {code : List Modules.Command} {seed final linked : Program} {exports : Environment} {all : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {resolved : ResolvedModule} (checked : resolve all linked = .ok resolved)
    (profile : Plan globals env commands seed code final exports) (table : PreservesDeclarations final resolved.program)
    (host : Catalog) (state : State) (frame : Frame globals state) (ready : Ready globals resolved.program env)
    (live : Live env state) :
    ∃ out, ExecutesAll globals state commands out ∧ Modules.Runs resolved.program host state code out ∧
      ∀ next, out = .ok () next → Ready globals resolved.program exports ∧ Live exports next := by
  induction profile generalizing state with
  | done => exact ⟨_, .done _, .done, fun _ same => by cases same; exact ⟨ready, live⟩⟩
  | define root suffix ih =>
    have known : PreservesDeclarations root.table resolved.program :=
      fun id declaration found => table id declaration (preserves suffix id declaration found)
    obtain ⟨out, ran, native, kept⟩ :=
      reached_definition root resolved.program host (root_found known) frame live (known_globals ready)
    cases out with
    | error error reached => exact ⟨_, .failed ran, .failed native, fun _ no => nomatch no⟩
    | ok result reached =>
      cases result
      have ⟨nextFrame, nextLive⟩ := kept _ rfl
      have nextReady := ready_update ready root.site.target (some root.callable)
        (fun _ same => by cases same; exact root_linked known)
      obtain ⟨out, rest, nativeRest, completed⟩ := ih table reached nextFrame nextReady nextLive
      exact ⟨out, .step ran rest, .step native nativeRest, completed⟩
  | @assign _ name source rhs reads entry _ _ _ _ _ member related tracks suffix ih =>
    obtain ⟨result, ran, kept⟩ := Body.operand_total related state
    have native : ExecExpr resolved.program (List.range resolved.program.size) state rhs result :=
      .evaluates (calls := fun _ _ _ => False) (fun _ _ _ impossible => impossible.elim)
        (Body.evaluates_with _ _ _ ran)
    cases result with
    | error error reached => exact ⟨_, .failed (.assign ran), .failed (native_assignment _ _ _ _ _ _ native), fun _ no => nomatch no⟩
    | ok value reached =>
      have arrived := keep_frame frame kept
      have nextLive := write_live arrived (keep_live frame live (known_globals ready) kept)
        (known_globals ready) member value entry (copy_record tracks ran live)
      have nextReady := ready_update ready member entry (fun root equal => by
        cases tracks with
        | forget => cases equal
        | copy lookup => cases equal; exact (ready _ _ lookup).2)
      obtain ⟨out, sourceRest, nativeRest, completed⟩ := ih table _ (write_frame value arrived member) nextReady nextLive
      exact ⟨out, .step (.assign ran) sourceRest, .step (native_assignment _ _ _ _ _ _ native) nativeRest, completed⟩
  | invoke call callee tracked suffix ih =>
    have known := (ready _ _ tracked).2
    have found := known.1
    have permitted : callee.id ∈ List.range resolved.program.size :=
      List.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).choose
    obtain ⟨address, defining, loaded, ⟨record⟩⟩ := live _ _ tracked
    obtain ⟨result, ran, native, _, kept⟩ :=
      runs_at callee.site callee.BodyRuns checked callee.id found _ permitted (enter_callable checked known) (globalSlot call.callee)
        (read_global call.calleeGlobal loaded) record call.operands call.keywords call.star call.mapping
    cases result with
    | error error reached =>
      exact ⟨_, .failed (.invoke call callee ran), .failed (native_assignment _ _ _ _ _ _ native), fun _ no => nomatch no⟩
    | ok value reached =>
      have arrived := keep_frame frame kept
      have nextLive := write_live arrived (keep_live frame live (known_globals ready) kept)
        (known_globals ready) call.destinationGlobal value (callee.returned.map Callable.nested)
        (returned_record (call := call) ran)
      have nextReady := ready_update ready call.destinationGlobal (callee.returned.map Callable.nested) (returned_linked known)
      obtain ⟨out, sourceRest, nativeRest, completed⟩ :=
        ih table _ (write_frame value arrived call.destinationGlobal) nextReady nextLive
      exact ⟨out, .step (.invoke call callee ran) sourceRest, .step (native_assignment _ _ _ _ _ _ native) nativeRest, completed⟩

private theorem published_lookup (state : State) (name : String) (value : Value)
    (publicName : Modules.isPublic name = true) (loaded : state.bindingValue (globalSlot name) = .ok value)
    {globals : List String} (member : name ∈ globals) :
    (Modules.publish ⟨globals, [], []⟩ state).1.exports.lookup name = some value := by
  change ((globals.filterMap fun name =>
    (state.bindingValue (globalSlot name)).toOption.map (fun value => (name, value))).filter
      (fun pair => Modules.isPublic pair.1)).lookup name = some value
  induction globals with
  | nil => cases member
  | cons first rest ih =>
    by_cases same : name = first
    · subst first
      simp [loaded, Except.toOption, publicName]
    · have different : (name == first) = false := by simpa using same
      have remains : name ∈ rest := (List.mem_cons.mp member).resolve_left same
      have result := ih remains
      cases previous : state.bindingValue (globalSlot first) with
      | error => simpa [previous, Except.toOption] using result
      | ok =>
        cases visible : Modules.isPublic first <;>
          simpa [previous, Except.toOption, visible, List.lookup, different] using result

private theorem live_publication {globals : List String} {program : Program} {env : Environment}
    {source : Modules.Source} (names : source.globals = globals) (caller state : State)
    (ready : Ready globals program env) (live : Live env state) :
    PublishedLive env program (Modules.publish source state).1
      (Modules.restoreThread caller (Modules.publish source state).2) := by
  intro name callee known publicName
  obtain ⟨member, linked⟩ := ready name callee known
  obtain ⟨address, defining, loaded, ⟨record⟩⟩ := live name callee known
  have global : (name, Lists.Value.function address) ∈ Modules.globalValues source state :=
    List.mem_filterMap.mpr ⟨name, names ▸ member, by simp [loaded, Except.toOption]⟩
  have exported : (Modules.publish source state).1.exports.lookup name = some (.function address) := by
    obtain ⟨sourceGlobals, temps, commands⟩ := source
    exact published_lookup state name _ publicName loaded (show name ∈ sourceGlobals from (show sourceGlobals = globals from names) ▸ member)
  let roots := (Modules.globalValues source state).map Prod.snd
  have root : address ∈ roots.filterMap Lists.Value.address? :=
    List.mem_filterMap.mpr ⟨_, List.mem_map_of_mem global, rfl⟩
  have frozen := (Lists.freezes_iff_freeze state.heap (roots.filterMap Lists.Value.address?) _).mpr rfl
  obtain ⟨flag, stored, iff⟩ := frozen.cell address _ record.recorded
  have yes := iff.mpr (Or.inr (.root (Array.getElem?_eq_some_iff.mp record.recorded).choose root))
  subst flag
  refine ⟨linked, address, defining, exported, { record with frozen := true, recorded := stored, live := ?_ }, rfl⟩
  intro capture member
  obtain ⟨value, _, cell⟩ := record.live capture member
  obtain ⟨flag, stored, _⟩ := frozen.cell capture.address _ cell
  exact ⟨value, flag, stored⟩

theorem module_agrees {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (checked : resolve commands linked = .ok resolved) (host : Catalog) (caller : State) :
    ∃ reached, ExecutesAll (Trace.names commands) (enter resolved.source caller) commands reached ∧
      Modules.Runs resolved.program host (enter resolved.source caller) resolved.source.commands reached ∧
      Modules.Initializes resolved.program host resolved.source caller (finish resolved.source caller reached) ∧
      runModule commands host caller linked = .ok (finish resolved.source caller reached) ∧
      ∀ published finished, finish resolved.source caller reached = .ok published finished →
        PublishedLive exports resolved.program published finished := by
  have declared := plan_declares profile
  have detail := checked_of_resolve checked
  have elaborated : elaborateCommands commands linked = .ok (code, final) := by
    rw [elaborateCommands, Block.moduleBlock_eq declared]
    exact plan_compiles profile
  obtain ⟨sameCode, sameTable⟩ := Prod.mk.inj (Except.ok.inj (detail.1.symm.trans elaborated))
  have table : PreservesDeclarations final resolved.program := by
    rw [sameTable]
    exact fun _ _ found => found
  obtain ⟨reached, source, ran, completed⟩ := run_plan checked profile table host _ (entry_frame declared checked caller)
    (fun _ _ no => nomatch no) (fun _ _ no => nomatch no)
  have native : Modules.Runs resolved.program host (enter resolved.source caller) resolved.source.commands reached := by
    rw [sameCode]
    exact ran
  have initialized : Modules.Initializes resolved.program host resolved.source caller (finish resolved.source caller reached) :=
    .run detail.2.2.2 native
  refine ⟨reached, source, native, initialized,
    (initializes_iff_runModule _ _ _ _ _).mp (.run checked initialized), ?_⟩
  intro published finished success
  cases reached with
  | error => cases success
  | ok result state =>
    cases result
    cases success
    obtain ⟨ready, live⟩ := completed _ rfl
    exact live_publication (Entry.checked_module_globals declared checked) caller state ready live

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
