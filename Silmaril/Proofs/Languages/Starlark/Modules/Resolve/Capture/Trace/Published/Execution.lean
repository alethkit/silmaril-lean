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
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named (runs_at)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome Cell Capture)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

local notation "Value" => Lists.Value
local notation "SuiteRuns" =>
  Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Runs

private abbrev Ready {globals : List String} (program : Program) (env : Environment globals) : Prop :=
  ∀ name root, env name = some root → name ∈ globals ∧ PreservesDeclarations root.table program

private theorem ready_update {globals : List String} {program : Program} {env : Environment globals}
    (ready : Ready program env) {name : String} (member : name ∈ globals) (entry : Option (Root globals))
    (new : ∀ root, entry = some root → PreservesDeclarations root.table program) :
    Ready program (update env name entry) := by
  intro read root tracked
  by_cases same : read = name
  · subst read
    exact ⟨member, new root (by simpa [update] using tracked)⟩
  · exact ready read root (by simpa [update, same] using tracked)

private theorem known_globals {globals : List String} {program : Program} {env : Environment globals}
    (ready : Ready program env) : ∀ name root, env name = some root → name ∈ globals :=
  fun name root found => (ready name root found).1

private theorem root_found {globals : List String} {root : Root globals} {program : Program}
    (known : PreservesDeclarations root.table program) : program[root.id]? = some root.site.declaration :=
  known _ _ Array.getElem?_push_size

private theorem root_enter {globals : List String} {root : Root globals}
    {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (known : PreservesDeclarations root.table resolved.program) :
    BodyEntry root.site resolved.program (List.range resolved.program.size) root.id
      (fun state out => SuiteRuns root.site.block state root.site.source root.site.body.code out) := by
  have table : PreservesDeclarations root.bodyTable resolved.program := by
    intro id declaration found
    exact known _ _ (by simp [Root.table, Array.getElem?_push, Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp found).choose, found])
  have guarded :=
    Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.entry_guard
      root.suite table
  intro caller defining captures installed live assigned
  obtain ⟨out, ran, _, kept, exec, _⟩ :=
    Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.runs_activated
      root.site root.suite checked table _ guarded caller defining captures installed live assigned
  exact ⟨out, ran, exec, Body.returned_keeps caller root.site.declaration captures assigned out kept⟩

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

private theorem copy_record {globals : List String} {env : Environment globals} {state middle : State}
    {source : Lowering.Resolve.SourceExpr} {code : Lowering.Expr} {entry : Option (Root globals)} {value : Value}
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

private theorem reached_definition {globals : List String} {env : Environment globals} {state : State}
    (root : Root globals) (program : Program) (host : Catalog)
    (found : program[root.id]? = some root.site.declaration)
    (frame : Frame globals state) (live : Live env state)
    (tracked : ∀ name root, env name = some root → name ∈ globals) :
    ∃ out, Executes globals state root.command out ∧
      Modules.Executes program host state (.exec (.define root.site.name root.id)) out ∧
      (∀ next, out = .ok () next → Frame globals next ∧ Live (update env root.site.name (some root)) next) := by
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
        (some root) (fun known equal => by cases equal; exact ⟨_, _, rfl, ⟨record⟩⟩)⟩

private theorem run_plan {globals : List String} {env : Environment globals} {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {code : List Modules.Command} {seed final linked : Program} {all : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {resolved : ResolvedModule} (checked : resolve all linked = .ok resolved)
    (profile : Plan globals env commands seed code final) (table : PreservesDeclarations final resolved.program)
    (host : Catalog) (state : State) (frame : Frame globals state) (ready : Ready resolved.program env)
    (live : Live env state) :
    ∃ out, ExecutesAll globals state commands out ∧ Modules.Runs resolved.program host state code out := by
  induction profile generalizing state with
  | done => exact ⟨_, .done _, .done⟩
  | define root suffix ih =>
    have known : PreservesDeclarations root.table resolved.program :=
      fun id declaration found => table id declaration (preserves suffix id declaration found)
    obtain ⟨out, ran, native, kept⟩ :=
      reached_definition root resolved.program host (root_found known) frame live (known_globals ready)
    cases out with
    | error error reached => exact ⟨_, .failed ran, .failed native⟩
    | ok result reached =>
      cases result
      have ⟨nextFrame, nextLive⟩ := kept _ rfl
      have nextReady := ready_update ready root.site.target (some root) (fun _ same => by cases same; exact known)
      obtain ⟨out, rest, nativeRest⟩ := ih table reached nextFrame nextReady nextLive
      exact ⟨out, .step ran rest, .step native nativeRest⟩
  | @assign _ name source rhs reads entry _ _ _ _ member related tracks suffix ih =>
    obtain ⟨result, ran, kept⟩ := Body.operand_total related state
    have native : ExecExpr resolved.program (List.range resolved.program.size) state rhs result :=
      .evaluates (calls := fun _ _ _ => False) (fun _ _ _ impossible => impossible.elim)
        (Body.evaluates_with _ _ _ ran)
    cases result with
    | error error reached => exact ⟨_, .failed (.assign ran), .failed (native_assignment _ _ _ _ _ _ native)⟩
    | ok value reached =>
      have arrived := keep_frame frame kept
      have nextLive := write_live arrived (keep_live frame live (known_globals ready) kept)
        (known_globals ready) member value entry (copy_record tracks ran live)
      have nextReady := ready_update ready member entry (fun root equal => by
        cases tracks with
        | forget => cases equal
        | copy lookup => cases equal; exact (ready _ _ lookup).2)
      obtain ⟨out, sourceRest, nativeRest⟩ := ih table _ (write_frame value arrived member) nextReady nextLive
      exact ⟨out, .step (.assign ran) sourceRest, .step (native_assignment _ _ _ _ _ _ native) nativeRest⟩
  | invoke call root tracked suffix ih =>
    have known := (ready _ _ tracked).2
    have found := root_found known
    have permitted : root.id ∈ List.range resolved.program.size :=
      List.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).choose
    obtain ⟨address, defining, loaded, ⟨record⟩⟩ := live _ _ tracked
    obtain ⟨result, ran, native, _, kept⟩ :=
      runs_at root.site _ checked root.id found _ permitted (root_enter checked known) (globalSlot call.callee)
        (read_global call.calleeGlobal loaded) record call.operands call.keywords call.star call.mapping
    cases result with
    | error error reached =>
      exact ⟨_, .failed (.invoke call root ran), .failed (native_assignment _ _ _ _ _ _ native)⟩
    | ok value reached =>
      have arrived := keep_frame frame kept
      have nextLive := write_live arrived (keep_live frame live (known_globals ready) kept)
        (known_globals ready) call.destinationGlobal value none (fun _ no => nomatch no)
      have nextReady := ready_update ready call.destinationGlobal none (fun _ no => nomatch no)
      obtain ⟨out, sourceRest, nativeRest⟩ :=
        ih table _ (write_frame value arrived call.destinationGlobal) nextReady nextLive
      exact ⟨out, .step (.invoke call root ran) sourceRest, .step (native_assignment _ _ _ _ _ _ native) nativeRest⟩

theorem module_agrees {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final)
    (checked : resolve commands linked = .ok resolved) (host : Catalog) (caller : State) :
    ∃ reached, ExecutesAll (Trace.names commands) (enter resolved.source caller) commands reached ∧
      Modules.Runs resolved.program host (enter resolved.source caller) resolved.source.commands reached ∧
      Modules.Initializes resolved.program host resolved.source caller (finish resolved.source caller reached) ∧
      runModule commands host caller linked = .ok (finish resolved.source caller reached) := by
  have declared := plan_declares profile
  have detail := checked_of_resolve checked
  have elaborated : elaborateCommands commands linked = .ok (code, final) := by
    rw [elaborateCommands, Block.moduleBlock_eq declared]
    exact plan_compiles profile
  obtain ⟨sameCode, sameTable⟩ := Prod.mk.inj (Except.ok.inj (detail.1.symm.trans elaborated))
  have table : PreservesDeclarations final resolved.program := by
    rw [sameTable]
    exact fun _ _ found => found
  obtain ⟨reached, source, ran⟩ := run_plan checked profile table host _ (entry_frame declared checked caller)
    (fun _ _ no => nomatch no) (fun _ _ no => nomatch no)
  have native : Modules.Runs resolved.program host (enter resolved.source caller) resolved.source.commands reached := by
    rw [sameCode]
    exact ran
  have initialized : Modules.Initializes resolved.program host resolved.source caller (finish resolved.source caller reached) :=
    .run detail.2.2.2 native
  exact ⟨reached, source, native, initialized,
    (initializes_iff_runModule _ _ _ _ _).mp (.run checked initialized)⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
