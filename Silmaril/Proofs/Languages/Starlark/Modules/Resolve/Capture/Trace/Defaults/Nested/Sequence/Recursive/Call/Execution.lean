module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Operands
public import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (Site Elaborates Emissions)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome Value Capture Cell)
open Silmaril.Languages.Starlark.Lists.Iteration (finishState)

local notation "NormalizedExpr" => Lowering.Resolve.SourceExpr

private theorem positioned {codes : List Lowering.Expr} {values : List Value} (state : State)
    (length : values.length = codes.length) :
    Lowering.Expands ((Lowering.argumentShape codes [] none none).collect values) state (.ok ⟨values, []⟩ state) := by
  have shape : (Lowering.argumentShape codes [] none none).collect values = ⟨values, [], none, none⟩ := by
    simp [Lowering.argumentShape, ArgumentShape.collect, ← length]
  rw [shape]
  simpa only [List.append_nil] using Lowering.Expands.success (args := ⟨values, [], none, none⟩) (keys := [])
    (values := []) (next := state) rfl .empty

private def keep_record {parent : LexicalBlock} {site : Site parent} {id : DeclarationId}
    {defining state next : State} {address : Nat} (record : ClosureAt site id defining state address)
    (kept : Body.Keeps state.heap.size state next) : ClosureAt site id defining next address :=
  { record with
    recorded := kept.2 _ _ (Array.getElem?_eq_some_iff.mp record.recorded).choose record.recorded
    live := fun capture present => by
      obtain ⟨value, frozen, found⟩ := record.live capture present
      exact ⟨value, frozen, kept.2 _ _ (Array.getElem?_eq_some_iff.mp found).choose found⟩ }

private abbrev Operational (program : Program) (available : List DeclarationId) :=
  Lowering.EvaluatesWith program available (Lowering.coreClosureRuns program available) (fun _ => True)

private theorem agreement {program : Program} {available : List DeclarationId}
    {state : State} {code : Lowering.Expr} {out : Outcome Value}
    (ran : Operational program available state code out) :
    ExecExpr program available state code out ∧ Lowering.denoteExpr program available code state = out :=
  ⟨.evaluates (fun _ _ _ call => call) ran,
    Lowering.denoteExprWith_eq_of_evaluates (fun _ _ _ call => (exec_iff_denoteBody _ _ _ _ _).mp call) ran⟩

theorem callee_error {parent block : LexicalBlock} (site : Site parent) (id : DeclarationId)
    (program : Program) (available : List DeclarationId) {name : String}
    (owned : name ∈ block.owned) (arguments : List NormalizedExpr) (codes : List Lowering.Expr)
    {state : State} {error : Silmaril.Languages.Starlark.Lists.Error}
    (failed : state.bindingValue (fileSlot name) = .error error) :
    Runs site block id name arguments codes state (.error error state) ∧
      ExecExpr program available state (expression name codes) (.error error state) ∧
      Lowering.denoteExpr program available (expression name codes) state = .error error state := by
  have read : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand (fileSlot name))
      (state.read (.bound (fileSlot name))) := .read (.owned owned)
  rw [State.read] at read
  simp only [failed] at read
  have native : Operational program available state (expression name codes) (.error error state) := by
    apply Lowering.EvaluatesWith.callError
    simpa only [Lowering.sourceOperands, List.map_nil, Option.toList_none, List.append_nil] using
      Lowering.EvaluatesManyWith.headError (tail := codes) (Body.evaluates_with program available _ read)
  exact ⟨.calleeError read, agreement native⟩

theorem runs_preserving {parent block : LexicalBlock} (site : Site parent) {seed final : Program} {emissions : Emissions}
    (profile : Elaborates site.block site.source seed site.body final emissions)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations final resolved.program)
    (id : DeclarationId) (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    {name : String} {state defining : State} {address : Nat}
    (callee : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand (fileSlot name))
      (.ok (.function address) state))
    (record : ClosureAt site id defining state address)
    {arguments : List NormalizedExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Arguments block arguments codes reads) :
    ∃ out, Runs site block id name arguments codes state out ∧
      ExecExpr resolved.program available state (expression name codes) out ∧
      Lowering.denoteExpr resolved.program available (expression name codes) state = out ∧
      Body.Keeps state.heap.size state (finishState out) := by
  let program := resolved.program
  let calls := Lowering.coreClosureRuns program available
  have read := Body.evaluates_with program available calls callee
  obtain ⟨operands, ran, kept, length⟩ := arguments_total related state
  have applyCall {actualState : State} {values : List Value} {out : Outcome Value}
      (evaluated : Evaluates block state arguments codes (.ok values actualState))
      (size : values.length = codes.length)
      (dispatch : Lowering.DispatchesWith program available calls actualState (.function address) ⟨values, []⟩ out) :
      Operational program available state (expression name codes) out := by
    apply Lowering.EvaluatesWith.call
    · simpa only [Lowering.sourceOperands, List.map_nil, Option.toList_none, List.append_nil] using
        Lowering.EvaluatesManyWith.cons read (evaluates_many program available calls evaluated)
    · exact .expanded (positioned actualState size) dispatch
  cases operands with
  | error error residual =>
    have native : Operational program available state (expression name codes) (.error error residual) := by
      apply Lowering.EvaluatesWith.callError
      simpa only [Lowering.sourceOperands, List.map_nil, Option.toList_none, List.append_nil] using
        Lowering.EvaluatesManyWith.tailError read (evaluates_many program available calls ran)
    exact ⟨_, .operandError callee ran, (agreement native).1, (agreement native).2, kept⟩
  | ok values actualState =>
    let reached := keep_record record kept
    obtain ⟨bound, binds⟩ :=
      Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.binds_total
        (site.parameters.slots reached.defaults) values
    have codeLength : (site.defaults.map PlainPositionalDefault.value).length = site.parameters.optional.length := by
      simpa using congrArg List.length (Lexical.translates site.lexical).1
    have ready :=
      Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.checked_prepare_positional
        checked id available permitted site.parameters site.declaration _ found rfl codeLength actualState
        address reached.frozen reached.captures reached.defaults values reached.length reached.recorded binds
    cases bound with
    | error error =>
      have ⟨native, meaning⟩ := agreement (applyCall ran (length _ _ rfl) (.reject ready))
      exact ⟨_, .bindingError callee ran reached binds, native, meaning, kept⟩
    | ok assigned =>
      obtain ⟨out, bodyRun, _, executable, _, restored⟩ :=
        Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.runs_activated
          site profile program table (withoutDeclaration available id) actualState defining reached.captures
          reached.installed reached.live assigned
      have dispatch : Lowering.DispatchesWith program available calls actualState (.function address)
          ⟨values, []⟩ (Leaf.returnTo actualState out) := by
        cases out with
        | ok flow final => exact .returned ready executable
        | error error final => exact .failed ready executable
      have ⟨native, meaning⟩ := agreement (applyCall ran (length _ _ rfl) dispatch)
      refine ⟨_, .invoked callee ran reached binds bodyRun, native, meaning, restored.1.trans kept.1, ?_⟩
      intro address cell low found
      exact restored.2.2 address cell (kept.2 address cell low found)

theorem runs {parent block : LexicalBlock} (site : Site parent) {seed final : Program} {emissions : Emissions}
    (profile : Elaborates site.block site.source seed site.body final emissions)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations final resolved.program)
    (id : DeclarationId) (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    {name : String} {state defining : State} {address : Nat}
    (callee : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand (fileSlot name))
      (.ok (.function address) state))
    (record : ClosureAt site id defining state address)
    {arguments : List NormalizedExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Arguments block arguments codes reads) :
    ∃ out, Runs site block id name arguments codes state out ∧
      ExecExpr resolved.program available state (expression name codes) out ∧
      Lowering.denoteExpr resolved.program available (expression name codes) state = out := by
  obtain ⟨out, source, native, meaning, _⟩ :=
    runs_preserving site profile checked table id found available permitted callee record related
  exact ⟨out, source, native, meaning⟩

private theorem installed_cells {parent : LexicalBlock} (site : Site parent)
    {id : DeclarationId} {defining installed : State} {captures : List Capture}
    (step : Nested.SiteResult parent site.name site.parameters site.defaults id captures defining (.ok .next installed))
    (cells : Body.CaptureCells defining captures) : Body.CaptureCells installed captures := by
  cases step with
  | @installed saved next evaluated ran exactState _ _ =>
    rw [exactState]
    let record : Cell := ⟨.function ⟨id, captures,
      (site.parameters.optional.map (fileSlot ∘ Prod.fst)).zip saved⟩, false⟩
    let grown : State := { evaluated with heap := evaluated.heap.push record }
    have kept := Lexical.evaluates_keeps site.lexical ran
    have live : Body.CaptureCells grown captures := by
      intro capture member
      obtain ⟨value, frozen, found⟩ := cells capture member
      have reached : evaluated.heap[capture.address]? = some ⟨.binding value, frozen⟩ :=
        kept.2 _ _ (Array.getElem?_eq_some_iff.mp found).choose found
      have within := (Array.getElem?_eq_some_iff.mp reached).choose
      exact ⟨value, frozen, by simp [grown, Array.getElem?_push, Nat.ne_of_lt within, reached]⟩
    exact Body.capture_cells_written grown (fileSlot site.name) (.function evaluated.heap.size) live

theorem runs_installed_alias_preserving {parent : LexicalBlock} (site : Site parent)
    {seed final : Program} {emissions : Emissions}
    (profile : Elaborates site.block site.source seed site.body final emissions)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations final resolved.program)
    (id : DeclarationId) (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    {defining installed : State} {captures : List Capture}
    (step : Nested.SiteResult parent site.name site.parameters site.defaults id captures defining (.ok .next installed))
    (receipts : Installs defining site.free captures) (cells : Body.CaptureCells defining captures)
    {name : String} (owned : name ∈ parent.owned) (legal : name.toList.head? ≠ some '$')
    {free : List FreeName} {floor : Nat} (frame : Body.Frame parent free floor installed)
    {arguments : List NormalizedExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Arguments parent arguments codes reads) :
    ∃ address out, Body.Evaluates parent installed (.scalar (.read site.name)) (Leaf.readOperand (fileSlot site.name))
        (.ok (.function address) installed) ∧
      (let copied := installed.write (fileSlot name) (.function address)
       (Lowering.Resolve.resolveTracked parent.context (.call (.scalar (.read name)) arguments [] none none) =
          .ok (expression name codes, fileSlot name :: reads)) ∧
       Runs site parent id name arguments codes copied out ∧
       ExecExpr resolved.program available copied (expression name codes) out ∧
       Lowering.denoteExpr resolved.program available (expression name codes) copied = out ∧ Body.Keeps copied.heap.size copied (finishState out)) := by
  obtain ⟨address, saved, evaluated, evaluatedDefaults, first, read, exactRecord⟩ :=
    Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.reads_installed_alias_defaults
      site.target owned frame step
  let origin : ClosureAt site id defining (installed.write (fileSlot name) (.function address)) address :=
    ⟨captures, saved, false, Lexical.evaluated_length site.lexical evaluatedDefaults, exactRecord, receipts,
      Body.capture_cells_written installed (fileSlot name) (.function address) (installed_cells site step cells)⟩
  obtain ⟨out, ran, operated, denoted, kept⟩ :=
    runs_preserving site profile checked table id found available permitted read origin related
  exact ⟨address, out, first, resolves legal owned related, ran, operated, denoted, kept⟩

theorem runs_installed_alias {parent : LexicalBlock} (site : Site parent)
    {seed final : Program} {emissions : Emissions}
    (profile : Elaborates site.block site.source seed site.body final emissions)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations final resolved.program)
    (id : DeclarationId) (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    {defining installed : State} {captures : List Capture}
    (step : Nested.SiteResult parent site.name site.parameters site.defaults id captures defining (.ok .next installed))
    (receipts : Installs defining site.free captures) (cells : Body.CaptureCells defining captures)
    {name : String} (owned : name ∈ parent.owned) (legal : name.toList.head? ≠ some '$')
    {free : List FreeName} {floor : Nat} (frame : Body.Frame parent free floor installed)
    {arguments : List NormalizedExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Arguments parent arguments codes reads) :
    ∃ address out, Body.Evaluates parent installed (.scalar (.read site.name)) (Leaf.readOperand (fileSlot site.name))
        (.ok (.function address) installed) ∧
      (let copied := installed.write (fileSlot name) (.function address)
       (Lowering.Resolve.resolveTracked parent.context (.call (.scalar (.read name)) arguments [] none none) =
          .ok (expression name codes, fileSlot name :: reads)) ∧
       Runs site parent id name arguments codes copied out ∧
       ExecExpr resolved.program available copied (expression name codes) out ∧
       Lowering.denoteExpr resolved.program available (expression name codes) copied = out) := by
  obtain ⟨address, out, first, translated, ran, native, meaning, _⟩ :=
    runs_installed_alias_preserving site profile checked table id found available permitted step receipts cells owned legal frame related
  exact ⟨address, out, first, translated, ran, native, meaning⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call
