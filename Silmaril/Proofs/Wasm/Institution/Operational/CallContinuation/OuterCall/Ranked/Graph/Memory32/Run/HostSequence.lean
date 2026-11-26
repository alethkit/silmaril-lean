module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Sequence.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Body.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.V1.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.HostEntry
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.HostControl
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Guard

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.Sequence.Proofs

open Execution.Runtime (AdminInstr EvalCtx Frame MemAddr MemInst Value)
open Computed
open Wasm.V1.Execution
open ControlProofs
open HostEntry.Proofs (invoke_exact literal_expression numeric_expression framed_numeric_step framed_direct_step
  framed_trapped_step bytes_unique)

private theorem encode_expression {H : Type} (seq : Sequence H) (rest : List (HostSegment H)) :
    expression (encode Graph.v1CodeSyntax.ops (v1Code seq.root.function.code) rest) = seq.continuation rest := by
  induction rest with
  | nil => rfl
  | cons segment rest ih =>
    change expression (segment.operands.map (Prefix.emit Graph.v1CodeSyntax.ops) ++
      .call segment.site.index :: encode Graph.v1CodeSyntax.ops (v1Code seq.root.function.code) rest) = _
    rw [expression_append, numeric_expression]
    exact congrArg (fun tail => segment.operands.map (Prefix.emit v1Syntax) ++ .source (.call segment.site.index) :: tail) ih

section Execution

variable {H : Type} {seq : Sequence H} {host : HostSemantics H} {mode : MemoryMode}
  {program : Program} {memory : MemAddr} {calls : CallMode} {base : Store H} {initial : MemInst}
  {start : ByteArray} {outer : Frame} {args : List Value} {path : List PathNode}

local notation "live" => storeWithBytes base memory initial
local notation "renderPhase" => seq.render base memory initial start outer args
local notation "active" => seq.root.function.declaration.frame args
local notation "arity" => seq.root.function.declaration.results.length
local notation "rootFn" => seq.root.function
local notation "contextAt" => OpenLabel.context (rootFn) args

private theorem render_begin (stack : List Value) (labels : List OpenLabel) (nodes : List PathNode) :
    renderPhase (seq.beginPath start stack labels nodes) =
      ⟨live start, outer, (contextAt labels).plug value (values stack ++ expression (seq.sourcePath nodes))⟩ := by
  cases nodes with
  | nil =>
    change renderPhase (.computing start stack seq.root.operands seq.root.site seq.later labels) =
      ⟨live start, outer, (contextAt labels).plug value
        (values stack ++ expression (encode Graph.v1CodeSyntax.ops (v1Code (rootFn).code) (seq.first :: seq.later)))⟩
    rw [encode_expression]
    simp only [continuation, encode, first, v1Syntax, Function.comp_apply, render, List.append_assoc]
  | cons node rest => rfl

private theorem enter_step {dst : Config H} (checked : seq.Checked mode program memory calls base outer args path) :
    Step host (renderPhase (.invoke path)) dst ↔
      dst = renderPhase (seq.beginPath start (rootFn).initial [] path) := by
  have count : args.length = (rootFn).declaration.params.length := by simpa using congrArg List.length checked.parameters
  have allocated : (live start).funcs[seq.root.address.value]? =
      some (.wasm (rootFn).declaration.type (rootFn).declaration.module (seq.v1FuncAt path)) := checked.allocated
  have body : expression (seq.v1FuncAt path).body =
      values (rootFn).initial ++ expression (seq.sourcePath path) := by
    change expression ((rootFn).initial.map Graph.v1CodeSyntax.ops.value ++ seq.sourcePath path) = _
    rw [expression_append, literal_expression]
  have locals : (seq.v1FuncAt path).locals = (rootFn).declaration.locals := rfl
  rw [render_begin]
  simpa only [render, body, locals, OpenLabel.context,
    OpenLabel.results, OpenLabel.insert, EvalCtx.comp, EvalCtx.plug, List.head?_nil,
    Option.map_none, Option.getD_none, Declaration.frame] using
    (invoke_exact (host := host) (outer := outer) (dst := dst) allocated count checked.scalar)

private theorem root_call {current : List PathNode} {dst : Config H}
    (checked : seq.Checked mode program memory calls base outer args path) :
    Step host (renderPhase (.call current)) dst ↔ dst = renderPhase (.invoke current) :=
  HostCall.V1.direct_step_iff (tail := []) checked.resolved

private theorem block_entry {stack : List Value} {block : PathBlock} {rest : List PathNode}
    {labels : List OpenLabel} {dst : Config H} :
    Step host (renderPhase (.path stack ⟨block, none⟩ rest labels)) dst ↔
      dst = renderPhase (seq.beginPath start [] (⟨stack, block⟩ :: labels) rest) := by
  rw [render_begin, open_code]
  exact scoped_block_iff (rootFn) args labels

private theorem condition_step {stack : List Value} {block : PathBlock} {choice : PathChoice}
    {rest : List PathNode} {condition : BitVec 32} {labels : List OpenLabel} {dst : Config H}
    (found : (active).locals[choice.condition.toNat]? = some (.int .i32 condition)) :
    Step host (renderPhase (.path stack ⟨block, some choice⟩ rest labels)) dst ↔
      dst = renderPhase (.test stack block choice rest condition labels) :=
  scoped_get_iff (rootFn) args labels found

private theorem path_select {stack : List Value} {block : PathBlock} {choice : PathChoice}
    {rest : List PathNode} {condition : BitVec 32} {labels : List OpenLabel} {dst : Config H} :
    Step host (renderPhase (.test stack block choice rest condition labels)) dst ↔
      dst = renderPhase (if condition = 0 then
        .graph ⟨start, outer, (contextAt labels).plug value
          (values stack ++ .source (.block block.result (v1Code choice.alternate)) :: expression (v1Code block.tail))⟩
        else .path stack ⟨block, none⟩ rest labels) := by
  have rule := scoped_if_iff (H := H) (host := host) (s := live start) (outer := outer) (rootFn) args labels
    (stack := stack) (condition := condition) (result := block.result) (left := seq.sourcePath rest)
    (right := v1Code choice.alternate) (tail := expression (v1Code block.tail)) (dst := dst)
  by_cases zero : condition = 0
  · simpa only [zero, ite_true, render, Memory32.render] using rule
  · rw [ite_eq_right zero] at rule ⊢
    exact rule

private theorem numeric_step {bytes : ByteArray} {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op}
    {site : HostCall.V1.Site H} {later : List (HostSegment H)} {labels : List OpenLabel} {dst : Config H} :
    Step host (renderPhase (.computing bytes stack (op :: rest) site later labels)) dst ↔
      (∃ next, Prefix.Reduce (active).locals stack op (.values next) ∧
        dst = renderPhase (.computing bytes next rest site later labels)) ∨
      (∃ saved, Prefix.Reduce (active).locals stack op (.trap saved) ∧
        dst = renderPhase (.trapped bytes saved (rest.map (Prefix.emit v1Syntax) ++
          .source (.call site.index) :: seq.continuation later) labels)) := by
  let tail := rest.map (Prefix.emit v1Syntax) ++ .source (.call site.index) :: seq.continuation later
  let output out := [AdminInstr.label (OpenLabel.results (rootFn) labels).length [] (Prefix.outcomeCode values .trap tail out)]
  have atLabel :
      ∀ target : Config H, Step host ⟨live bytes, outer, [.frame (OpenLabel.results (rootFn) labels).length active
        [.label (OpenLabel.results (rootFn) labels).length [] (values stack ++ Prefix.emit v1Syntax op :: tail)]]⟩ target ↔
        ∃ out, Prefix.Reduce (active).locals stack op out ∧ target = ⟨live bytes, outer,
          [.frame (OpenLabel.results (rootFn) labels).length active (output out)]⟩ := by
    intro target
    rw [framed_numeric_step]
    constructor
    · rintro (⟨next, move, eq⟩ | ⟨saved, move, eq⟩)
      · exact ⟨.values next, move, eq⟩
      · exact ⟨.trap saved, move, eq⟩
    · rintro ⟨out, move, eq⟩
      cases out with
      | values next => exact .inl ⟨next, move, eq⟩
      | trap saved => exact .inr ⟨saved, move, eq⟩
  simp only [render, List.map_cons, List.append_assoc, List.cons_append]
  change Step host ⟨live bytes, outer, (contextAt labels).plug value (values stack ++ Prefix.emit v1Syntax op :: tail)⟩ dst ↔ _
  rw [scoped_result (rootFn) args labels (fun out => Prefix.Reduce (active).locals stack op out) output atLabel]
  simp only [context_code]
  constructor
  · rintro ⟨out, move, eq⟩
    cases out with
    | values next => exact .inl ⟨next, move, eq⟩
    | trap saved => exact .inr ⟨saved, move, eq⟩
  · rintro (⟨next, move, eq⟩ | ⟨saved, move, eq⟩)
    · exact ⟨.values next, move, eq⟩
    · exact ⟨.trap saved, move, eq⟩

private theorem host_call {bytes : ByteArray} {saved actual : List Value} {site : HostCall.V1.Site H}
    {later : List (HostSegment H)} {labels : List OpenLabel} {dst : Config H}
    (linked : Linked site (rootFn).declaration.module base) :
    Step host (renderPhase (.computing bytes (saved ++ actual) [] site later labels)) dst ↔
      dst = renderPhase (.pending bytes saved actual site later labels) := by
  simp only [render, List.map_nil, List.append_nil]
  exact scoped_source_iff (rootFn) args labels rfl (by intro _ h; cases h) (by intro h; cases h)
    (fun _ => HostCall.V1.direct_step_iff (caller := active) linked.resolved)

private theorem trap_step {bytes : ByteArray} {saved : List Value} {tail : List Admin}
    {labels : List OpenLabel} {dst : Config H} :
    Step host (renderPhase (.trapped bytes saved tail labels)) dst ↔
      (∃ kept rest, Prefix.Discard saved tail kept rest ∧ dst = renderPhase (.trapped bytes kept rest labels)) ∨
      (saved = [] ∧ tail = [] ∧ dst = renderPhase (.graph ⟨bytes, outer, seq.afterLabel args labels [.trap]⟩)) := by
  let outcome : Option (List Value × List Admin) → List Admin
    | none => [.trap]
    | some (kept, rest) => [.label (OpenLabel.results (rootFn) labels).length [] (values kept ++ .trap :: rest)]
  let moves : Option (List Value × List Admin) → Prop
    | none => saved = [] ∧ tail = []
    | some (kept, rest) => Prefix.Discard saved tail kept rest
  have atLabel :
      ∀ target : Config H, Step host ⟨live bytes, outer, [.frame (OpenLabel.results (rootFn) labels).length active
        [.label (OpenLabel.results (rootFn) labels).length [] (values saved ++ .trap :: tail)]]⟩ target ↔
        ∃ out, moves out ∧ target = ⟨live bytes, outer,
          [.frame (OpenLabel.results (rootFn) labels).length active (outcome out)]⟩ := by
    intro target
    rw [framed_trapped_step]
    constructor
    · rintro (⟨kept, rest, move, eq⟩ | ⟨empty, noTail, eq⟩)
      · exact ⟨some (kept, rest), move, eq⟩
      · exact ⟨none, ⟨empty, noTail⟩, eq⟩
    · rintro ⟨out, move, eq⟩
      rcases out with _ | ⟨kept, rest⟩
      · exact .inr ⟨move.1, move.2, eq⟩
      · exact .inl ⟨kept, rest, move, eq⟩
  simp only [render, Memory32.render, afterLabel]
  rw [scoped_result (rootFn) args labels moves outcome atLabel]
  simp only [context_code]
  constructor
  · rintro ⟨out, move, eq⟩
    rcases out with _ | ⟨kept, rest⟩
    · exact .inr ⟨move.1, move.2, eq⟩
    · exact .inl ⟨kept, rest, move, eq⟩
  · rintro (⟨kept, rest, move, eq⟩ | ⟨empty, noTail, eq⟩)
    · exact ⟨some (kept, rest), move, eq⟩
    · exact ⟨none, ⟨empty, noTail⟩, eq⟩

private theorem render_delivered {bytes : ByteArray} {saved : List Value} {later : List (HostSegment H)}
    {labels : List OpenLabel} (r : Execution.Runtime.Result) :
    renderPhase (seq.delivered outer args bytes saved later r labels) =
      ⟨live bytes, outer, (contextAt labels).plug value (values saved ++ result r ++ seq.continuation later)⟩ := by
  cases r with
  | trap => simp [delivered, render, result, List.append_assoc]
  | values vs =>
    cases later <;> simp [delivered, resume, render, Memory32.render, continuation, encode, v1Syntax, result, List.append_assoc]

private theorem pending_step {bytes : ByteArray} {saved actual : List Value} {site : HostCall.V1.Site H}
    {later : List (HostSegment H)} {labels : List OpenLabel} {dst : Config H}
    (linked : Linked site (rootFn).declaration.module base)
    (typed : actual.map Value.type = site.signature.params) :
    Step host (renderPhase (.pending bytes saved actual site later labels)) dst ↔
      (∃ s' r, host site.target (live bytes) actual (.returned s' r) ∧
        dst = ⟨s', outer, (contextAt labels).plug value (values saved ++ result r ++ seq.continuation later)⟩) ∨
      (host site.target (live bytes) actual .diverged ∧
        dst = renderPhase (.pending bytes saved actual site later labels)) := by
  have siteChecked : site.Checked (live bytes) ((contextAt labels).activeFrame outer) actual := by
    rw [active_frame]
    exact ⟨linked.resolved, linked.allocated, typed, linked.scalar⟩
  exact v1_host_pending_step_iff (k := contextAt labels) (outer := outer)
    (saved := saved) (tail := seq.continuation later) siteChecked

private theorem label_scalar (checked : seq.Checked mode program memory calls base outer args path)
    (labels : List OpenLabel) : (OpenLabel.results (rootFn) labels).length ≤ 1 := by
  cases labels with
  | nil => exact checked.scalar
  | cons label rest => cases h : label.block.result <;> simp [OpenLabel.results, h]

private theorem insert_allowed (checked : seq.Checked mode program memory calls base outer args path)
    {labels : List OpenLabel} (scopes : OpenLabel.Allowed mode program memory calls (rootFn) labels)
    {code : List Admin} (body : CodeAllowedFor mode program memory calls (rootFn).rank (active).module code) :
    CodeAllowedFor mode program memory calls (rootFn).rank (active).module
      ((OpenLabel.insert (rootFn) labels).plug value code) := by
  induction labels generalizing code with
  | nil => exact body
  | cons label rest ih =>
    simp only [OpenLabel.insert, EvalCtx.plug_comp, EvalCtx.plug]
    apply ih (fun opened member => scopes opened (.tail _ member))
    exact RunProofs.single_allowed.mpr
      (.label (label_scalar checked rest)
        (RunProofs.append_allowed.mpr ⟨RunProofs.append_allowed.mpr ⟨RunProofs.values_allowed label.saved, body⟩,
          scopes label (.head _)⟩))

private theorem frame_allowed (checked : seq.Checked mode program memory calls base outer args path)
    {code : List Admin}
    (guard : CodeAllowedFor mode program memory calls (rootFn).rank (active).module code) :
    CodeAllowedFor mode program memory calls ((rootFn).rank + 1) outer.module
      [AdminInstr.frame arity active code] := by
  have rank : calls.permits ((rootFn).rank + 1) (rootFn).rank := by cases calls <;> simp [CallMode.permits]
  exact RunProofs.single_allowed.mpr (.enteredFrame checked.scalar rank guard)

private theorem wrap_checked (checked : seq.Checked mode program memory calls base outer args path)
    {labels : List OpenLabel} (scopes : OpenLabel.Allowed mode program memory calls (rootFn) labels)
    {code : List Admin} (guard : CodeAllowedFor mode program memory calls (rootFn).rank (active).module code) :
    CodeAllowedFor mode program memory calls ((rootFn).rank + 1) outer.module ((contextAt labels).plug value code) := by
  rw [context_code]
  exact frame_allowed checked (insert_allowed checked scopes
    (RunProofs.single_allowed.mpr (.label (label_scalar checked labels) guard)))

private theorem resume_ready (checked : seq.Checked mode program memory calls base outer args path)
    {bytes : ByteArray} {stack : List Value} {later : List (HostSegment H)} {labels : List OpenLabel}
    (extent : mode.extent initial.data.size bytes) (listed : ∀ piece ∈ later, piece.site ∈ seq.sites)
    (typed : checkRegion (rootFn) (Prefix.stackTypes stack) (OpenLabel.results (rootFn) labels)
      (OpenLabel.targets (rootFn) labels) later = true)
    (scopes : seq.ContextReady mode program memory calls labels) :
    seq.Ready mode program memory calls initial (seq.resume outer args bytes stack later labels) path := by
  cases later with
  | nil =>
    have tail : CodeAllowedFor mode program memory calls (rootFn).rank (active).module seq.root.tail := by
      apply RunProofs.tail_allowed (fn := rootFn) ?_ checked.slot checked.supportedTail
      intro target used
      obtain ⟨callee, found, _, linked, permitted⟩ := checked.linkedTail target used
      exact ⟨callee, found, linked, permitted⟩
    exact ⟨extent, wrap_checked checked scopes.2
      (RunProofs.append_allowed.mpr ⟨RunProofs.values_allowed stack, tail⟩)⟩
  | cons piece rest =>
    exact ⟨extent, listed piece (.head _), fun later used => listed later (.tail _ used), typed, scopes⟩

theorem return_ready (checked : seq.Checked mode program memory calls base outer args path)
    (layout : Layout program base memory initial) (contract : seq.Contract host mode memory initial base)
    {bytes : ByteArray} {saved actual : List Value} {site : HostCall.V1.Site H}
    {later : List (HostSegment H)} {labels : List OpenLabel} {after : Store H} {r : Execution.Runtime.Result}
    (ready : seq.Ready mode program memory calls initial (.pending bytes saved actual site later labels) path)
    (returned : host site.target (live bytes) actual (.returned after r)) :
    ∃ next, after = live next ∧ bytes.size ≤ next.size ∧ HostCall.V1.ResultTyped site.signature.results r ∧
      Layout program after memory { initial with data := next } ∧
      seq.Ready mode program memory calls initial (seq.delivered outer args next saved later r labels) path := by
  obtain ⟨extent, listed, laterListed, typedArgs, continuation, scopes⟩ := ready
  obtain ⟨typed, storeEffect⟩ := contract site listed bytes extent actual typedArgs after r returned
  obtain ⟨next, stored, newExtent, mono, allocation⟩ := layout.host_store extent storeEffect
  refine ⟨next, stored, mono, typed, allocation, ?_⟩
  cases r with
  | trap => exact ⟨newExtent, scopes⟩
  | values payload =>
    apply resume_ready checked newExtent laterListed _ scopes
    have payloadTyped : payload.map Value.type = site.signature.results := typed
    simpa [Prefix.stackTypes, payloadTyped] using continuation

private theorem begin_ready {nodes : List PathNode} {stack : List Value} {labels : List OpenLabel}
    (extent : mode.extent initial.data.size start)
    (ready : seq.PathReady mode program memory calls labels stack nodes) :
    seq.Ready mode program memory calls initial (seq.beginPath start stack labels nodes) path := by
  cases nodes with
  | nil =>
    exact ⟨extent, .head _, fun piece used => .tail _ (List.mem_map.mpr ⟨piece, used, rfl⟩), ready.2.2, ready.1⟩
  | cons node rest => exact ready

private theorem locals_typed (checked : seq.Checked mode program memory calls base outer args path) :
    (active).locals.map Value.type = (rootFn).declaration.params ++ (rootFn).declaration.locals := by
  simp [Declaration.frame, checked.parameters, Value.zero, List.map_map, Function.comp_def]

private theorem condition_found (checked : seq.Checked mode program memory calls base outer args path)
    {stack : List Value} {block : PathBlock} {choice : PathChoice}
    {rest : List PathNode} {labels : List OpenLabel}
    (ready : seq.PathReady mode program memory calls labels stack (⟨block, some choice⟩ :: rest)) :
    ∃ bits : BitVec 32, (active).locals[choice.condition.toNat]? = some (.int .i32 bits) := by
  have typed := ready.2.2
  simp only [checkPath, Option.all_some, Bool.and_eq_true_iff, decide_eq_true_eq] at typed
  have localType := typed.1.2.1
  rw [← locals_typed checked, List.getElem?_map] at localType
  generalize lookup : (active).locals[choice.condition.toNat]? = value at localType
  cases value with
  | none => simp at localType
  | some v =>
    have same : v.type = .int .i32 := by simpa using localType
    rcases v with ⟨type, bits⟩
    cases same
    exact ⟨bits, rfl⟩

theorem preserves (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args path)
    (layout : Layout program base memory initial) (extent : mode.extent initial.data.size start)
    (contract : seq.Contract host mode memory initial base) {src dst : Phase H}
    (edge : seq.Edge host mode program memory base initial start outer args src dst)
    (ready : seq.Ready mode program memory calls initial src path) :
    seq.Ready mode program memory calls initial dst path := by
  cases edge with
  | resolve => exact ready
  | enter =>
    cases ready
    exact begin_ready extent ⟨⟨trivial, by simp [OpenLabel.Allowed]⟩, checked.guardedPath, checked.typedBody⟩
  | openBlock =>
    obtain ⟨scopes, allowed, typed⟩ := ready
    simp only [checkPath, Option.all_none, Bool.and_true, Bool.and_eq_true_iff] at typed
    refine begin_ready extent ⟨⟨⟨typed.1, scopes.1⟩, ?_⟩, allowed.2.2, typed.2⟩
    intro label used
    rcases List.mem_cons.mp used with rfl | previous
    · exact allowed.1
    · exact scopes.2 label previous
  | readCondition _ => exact ready
  | choosePath _ =>
    obtain ⟨scopes, allowed, typed⟩ := ready
    simp only [checkPath, Bool.and_eq_true_iff] at typed
    refine ⟨scopes, ⟨allowed.1, by simp, allowed.2.2⟩, ?_⟩
    apply Bool.and_eq_true_iff.mpr
    exact ⟨Bool.and_eq_true_iff.mpr ⟨typed.1.1, rfl⟩, typed.2⟩
  | chooseAlternate =>
    obtain ⟨scopes, allowed, _⟩ := ready
    exact ⟨extent, wrap_checked checked scopes.2
      (RunProofs.append_allowed.mpr ⟨RunProofs.values_allowed _,
        RunProofs.append_allowed.mpr ⟨RunProofs.single_allowed.mpr
          (.source (.block (allowed.2.1 _ (by simp)))), allowed.1⟩⟩)⟩
  | numeric moved =>
    obtain ⟨current, listed, later, check, scopes⟩ := ready
    have locals := locals_typed checked
    refine ⟨current, listed, later, ?_, scopes⟩
    rw [← locals]
    exact check_prefix_preserves (locals.symm ▸ check) moved
  | prefixTrap _ => exact ⟨ready.1, ready.2.2.2.2⟩
  | discard _ => exact ready
  | closeTrap =>
    exact ⟨ready.1, frame_allowed checked (insert_allowed checked ready.2.2
      (RunProofs.single_allowed.mpr .trap))⟩
  | hostResolve typed =>
    obtain ⟨current, listed, later, check, scopes⟩ := ready
    exact ⟨current, listed, later, typed, check_prefix_resume check typed, scopes⟩
  | returned behavior stored =>
    obtain ⟨next, discovered, _, _, _, readyNext⟩ := return_ready checked layout contract ready behavior
    exact (bytes_unique layout (discovered.symm.trans stored)) ▸ readyNext
  | diverged _ => exact ready
  | graph moved => exact moved.ready graphChecked ready

private theorem sound (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args path)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    {src dst : Phase H} (edge : seq.Edge host mode program memory base initial start outer args src dst)
    (ready : seq.Ready mode program memory calls initial src path) :
    Step host (renderPhase src) (renderPhase dst) := by
  cases edge with
  | resolve => exact (root_call checked).mpr rfl
  | enter =>
    cases ready
    exact (enter_step checked).mpr rfl
  | openBlock => exact block_entry.mpr rfl
  | readCondition found => exact (condition_step found).mpr rfl
  | choosePath nonzero => exact path_select.mpr (by rw [ite_eq_right nonzero])
  | chooseAlternate => exact path_select.mpr (by rw [ite_eq_left rfl])
  | numeric moved => exact numeric_step.mpr (.inl ⟨_, moved, rfl⟩)
  | prefixTrap moved => exact numeric_step.mpr (.inr ⟨_, moved, rfl⟩)
  | discard moved => exact trap_step.mpr (.inl ⟨_, _, moved, rfl⟩)
  | closeTrap => exact trap_step.mpr (.inr ⟨rfl, rfl, rfl⟩)
  | hostResolve _ => exact (host_call (checked.linkedHosts _ ready.2.1)).mpr rfl
  | returned behavior stored =>
    obtain ⟨_, listed, _, arguments, _⟩ := ready
    exact (pending_step (checked.linkedHosts _ listed) arguments).mpr
      (.inl ⟨_, _, behavior, (render_delivered _).trans (by cases stored; rfl)⟩)
  | diverged behavior =>
    obtain ⟨_, listed, _, arguments, _⟩ := ready
    exact (pending_step (checked.linkedHosts _ listed) arguments).mpr (.inr ⟨behavior, rfl⟩)
  | graph moved =>
    exact Step.of_internal ((v1_step_iff_at graphChecked layout matched ready).mpr
      ⟨_, moved, moved.ready graphChecked ready, rfl⟩)

private theorem readback (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args path)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (contract : seq.Contract host mode memory initial base)
    {src : Phase H} (ready : seq.Ready mode program memory calls initial src path) {dst : Config H}
    (step : Step host (renderPhase src) dst) :
    ∃ next, seq.Edge host mode program memory base initial start outer args src next ∧ dst = renderPhase next := by
  cases src with
  | call current => exact ⟨_, .resolve, (root_call checked).mp step⟩
  | invoke current =>
    cases ready
    exact ⟨_, .enter, (enter_step checked).mp step⟩
  | path stack node rest labels =>
    rcases node with ⟨block, _ | choice⟩
    · exact ⟨_, .openBlock, block_entry.mp step⟩
    · obtain ⟨bits, found⟩ := condition_found checked ready
      exact ⟨_, .readCondition found, (condition_step found).mp step⟩
  | test stack block choice rest condition labels =>
    by_cases zero : condition = 0
    · subst condition
      exact ⟨_, .chooseAlternate, by simpa only [ite_true] using path_select.mp step⟩
    · exact ⟨_, .choosePath zero, by simpa only [ite_eq_right zero] using path_select.mp step⟩
  | computing bytes stack remaining site later labels =>
    cases remaining with
    | nil =>
      obtain ⟨saved, actual, rfl, typed, _⟩ := check_prefix_arguments ready.2.2.2.1
      exact ⟨_, .hostResolve typed, (host_call (checked.linkedHosts _ ready.2.1)).mp step⟩
    | cons op rest =>
      rcases numeric_step.mp step with ⟨next, moved, eq⟩ | ⟨saved, trapped, eq⟩
      · exact ⟨_, .numeric moved, eq⟩
      · exact ⟨_, .prefixTrap trapped, eq⟩
  | trapped bytes saved tail labels =>
    rcases trap_step.mp step with ⟨kept, rest, discarded, eq⟩ | ⟨rfl, rfl, eq⟩
    · exact ⟨_, .discard discarded, eq⟩
    · exact ⟨_, .closeTrap, eq⟩
  | pending bytes saved actual site later labels =>
    have ⟨_, listed, _, arguments, _⟩ := ready
    rcases (pending_step (checked.linkedHosts site listed) arguments).mp step with
      ⟨after, r, returned, eq⟩ | ⟨diverged, eq⟩
    · obtain ⟨next, stored, _, _, _, _⟩ := return_ready checked layout contract ready returned
      refine ⟨_, .returned returned stored, ?_⟩
      rw [render_delivered]
      rw [stored] at eq
      exact eq
    · exact ⟨_, .diverged diverged, eq⟩
  | graph state =>
    have internal := (ReadyFor.internal_iff layout ready).mp step
    obtain ⟨next, moved, _, eq⟩ := (v1_step_iff_at graphChecked layout matched ready).mp internal
    exact ⟨.graph next, .graph moved, eq⟩

theorem step_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args path)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size start) (contract : seq.Contract host mode memory initial base)
    {src : Phase H} (ready : seq.Ready mode program memory calls initial src path) {dst : Config H} :
    Step host (renderPhase src) dst ↔
      ∃ next, seq.Edge host mode program memory base initial start outer args src next ∧
        seq.Ready mode program memory calls initial next path ∧ dst = renderPhase next := by
  constructor
  · intro step
    obtain ⟨next, moved, eq⟩ := readback graphChecked checked layout matched contract ready step
    exact ⟨next, moved, preserves graphChecked checked layout extent contract moved ready, eq⟩
  · rintro ⟨next, moved, _, rfl⟩
    exact sound graphChecked checked layout matched moved ready

theorem trapped_run {bytes : ByteArray} {saved : List Value} {tail : List Admin} {labels : List OpenLabel} {dst : Phase H}
    (run : seq.Runs host mode program memory base initial start outer args (.trapped bytes saved tail labels) dst) :
    (∃ saved rest, dst = .trapped bytes saved rest labels) ∨ ∃ state, dst = .graph state := by
  induction run with
  | refl => exact .inl ⟨saved, tail, rfl⟩
  | tail _ transition ih =>
    rcases ih with ⟨saved, rest, rfl⟩ | ⟨state, rfl⟩
    · cases transition with
      | discard _ => exact .inl ⟨_, _, rfl⟩
      | closeTrap => exact .inr ⟨_, rfl⟩
    · cases transition with
      | graph _ => exact .inr ⟨_, rfl⟩

theorem run_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args path)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size start) (contract : seq.Contract host mode memory initial base)
    {src : Phase H} (ready : seq.Ready mode program memory calls initial src path) {dst : Config H} :
    Steps host (renderPhase src) dst ↔
      ∃ next, seq.Runs host mode program memory base initial start outer args src next ∧
        seq.Ready mode program memory calls initial next path ∧ dst = renderPhase next :=
  HostEntry.Proofs.finite_run_iff renderPhase _ _
    (fun {_ _} h => step_iff graphChecked checked layout matched extent contract h)
    (fun step h => preserves graphChecked checked layout extent contract step h) ready

end Execution
end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.Sequence.Proofs
