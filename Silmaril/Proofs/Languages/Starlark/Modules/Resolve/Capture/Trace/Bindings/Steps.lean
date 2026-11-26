module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Heap
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Steps

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings

open Silmaril.Languages.Starlark.Modules (globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Cell Capture)

local notation "Value" => Silmaril.Languages.Starlark.Lists.Value

private theorem legal_cons {head : String} {tail : List String}
    (first : head.toList.head? ≠ some '$') (rest : ∀ name ∈ tail, name.toList.head? ≠ some '$') :
    ∀ name ∈ head :: tail, name.toList.head? ≠ some '$' := by
  intro name present
  rcases List.mem_cons.mp present with rfl | later
  · exact first
  · exact rest _ later

theorem schedule_static {globals : List String} {entries : Environment} {commands : List Command}
    (schedule : Bindings.Schedule globals entries commands) :
    ModuleBinders commands (names commands) ∧ RootCall.Segment globals commands ∧
      (∀ name ∈ names commands, name.toList.head? ≠ some '$') := by
  induction schedule with
  | nil => exact ⟨.nil, .nil, by simp [names]⟩
  | define known body _ ih =>
    exact ⟨.cons (.define _ _ _) ih.1,
      .define _ (fun program => definitions_accept body program [] (fun _ => Iff.rfl)) ih.2.1,
      legal_cons known.2 ih.2.2⟩
  | setup known _ _ ih | copy _ known _ _ ih | wrapper _ known _ _ _ ih | leaf _ known _ _ _ ih =>
    exact ⟨.cons (.assign _ _) ih.1, .assign _ _ ih.2.1, legal_cons known.2 ih.2.2⟩

theorem commit_live {globals : List String} {program : Program} {state : State} {name : String}
    {chain : Chain} {seed : Program} {frame : Frame} {rest : List Frame} {address : Nat} {captures : List Capture}
    (layout : ModuleSlots globals state) (member : name ∈ globals)
    (code : CallableCode globals program chain seed frame rest)
    (cell : state.heap[address]? = some ⟨.function ⟨(EmittedProgram seed rest).size, captures, []⟩, false⟩)
    (installed : ∃ owner, Installs owner frame.free captures)
    (legal : ∀ entry ∈ captures, entry.binding.name.toList.head? ≠ some '$') :
    LiveBinding globals program (state.write (globalSlot name) (.function address)) name chain := by
  obtain ⟨slot, _, _, owned, binding⟩ := layout.usable name member
  exact ⟨member, seed, frame, rest, address, captures, code,
    ⟨⟨slot, by rw [slots_write]; exact owned⟩, writes_binding _ _ _ _ owned binding,
      write_keeps_function _ _ _ _ _ _ cell⟩, installed, legal⟩

/-- After evaluating a RHS, every other tracked binding survives a named write.
Only the new value supplies the evidence for the destination. -/
theorem update_live {globals : List String} {program : Program} {entries : Environment}
    {state next : State} {name : String} {value : Value} {shape : Option Chain}
    (layout : ModuleSlots globals state) (pool : LiveBindings globals program entries state)
    (preserves : Preserves state next)
    (introduced : ∀ chain, shape = some chain →
      LiveBinding globals program (next.write (globalSlot name) value) name chain) :
    ModuleSlots globals (next.write (globalSlot name) value) ∧
      LiveBindings globals program (entries.write name shape) (next.write (globalSlot name) value) := by
  have kept := preserves.layout layout
  refine ⟨written_slots kept _ _, ?_⟩
  intro other chain tracked
  by_cases same : other = name
  · subst other
    exact introduced chain (by simpa [Environment.write] using tracked)
  · have known : entries other = some chain := by simpa [Environment.write, same] using tracked
    obtain ⟨member, seed, frame, rest, address, captures, code, live, installed, legal⟩ := pool other chain known
    have surviving := preserves.live layout member live
    exact ⟨member, seed, frame, rest, address, captures, code,
      (RootCall.write_keeps_live next other name value kept.distinct surviving (Ne.symm same)).2,
      installed, legal⟩

theorem retained_head {seed program : Program} {frame : Frame} {rest : List Frame}
    (keeps : Wrapper.KeepsTable seed program (frame :: rest)) :
    program[(EmittedProgram seed rest).size]? = some frame.declaration :=
  keeps _ _ (by simp [EmittedProgram])

theorem retained_tail {seed program : Program} {frame : Frame} {rest : List Frame}
    (keeps : Wrapper.KeepsTable seed program (frame :: rest)) : Wrapper.KeepsTable seed program rest := by
  intro index declaration found
  have within := (Array.getElem?_eq_some_iff.mp found).choose
  exact keeps _ _ (by simp [EmittedProgram, Array.getElem?_push, Nat.ne_of_lt within, found])

theorem define_step {before after : List Command} {chain : Chain} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ root chain :: after) globals)
    (checked : resolve (before ++ root chain :: after) linked = .ok resolved)
    (allowed : Definitions globals [] chain) (suffix : RootCall.Segment globals after)
    (globalsLegal : ∀ name ∈ globals, name.toList.head? ≠ some '$')
    (known : Visible globals chain.name) {state : State} {entries : Environment}
    (layout : ModuleSlots globals state) (pool : LiveBindings globals resolved.program entries state) :
    ∃ next, Leaf.Step resolved globals before.length state (root chain) (.ok () next) ∧
      (ModuleSlots globals next ∧ LiveBindings globals resolved.program (entries.write chain.name (some chain)) next) ∧
      Bindings.Writes state chain.name next := by
  obtain ⟨seed, frame, rest, emitted, links, scopes, site, kept⟩ :=
    RootCall.checked_definition_site before after chain globals linked resolved declared checked
      (fun program => definitions_accept allowed program [] (fun _ => Iff.rfl)) suffix
  obtain ⟨captures, installed⟩ : ∃ captures, Installs state frame.free captures := by
    apply installs_of_addresses
    intro entry present
    obtain ⟨name, member, describes⟩ := root_capture emitted entry present
    obtain ⟨address, _, _, slot, _⟩ := layout.usable name member
    exact ⟨globalSlot name, address, describes, .inl slot⟩
  let id := (EmittedProgram seed rest).size
  let cell : Cell := ⟨.function ⟨id, captures, []⟩, false⟩
  let grown : State := { state with heap := state.heap.push cell }
  let next := grown.write (globalSlot chain.name) (.function state.heap.size)
  have code : CallableCode globals resolved.program chain seed frame rest :=
    ⟨links, kept, [], [], (fun _ => Iff.rfl), allowed, emitted, scopes⟩
  have legal : ∀ entry ∈ captures, entry.binding.name.toList.head? ≠ some '$' := by
    apply captures_from_declared installed
    intro entry present
    obtain ⟨name, member, rfl⟩ := root_capture emitted entry present
    exact globalsLegal name member
  have preserves : Preserves state grown := Preserves.push state cell
  have owns : LiveBinding globals resolved.program next chain.name chain :=
    commit_live (preserves.layout layout) known.1 code (by simp [grown, cell, id]) ⟨state, installed⟩ legal
  exact ⟨next, .define site (retained_head kept) installed, update_live layout pool preserves (by
    intro other same
    cases same
    exact owns), .commit grown _ preserves⟩

theorem alias_step {before rest : List Command} {globals : List String} {source destination : String}
    {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ .assign destination (.scalar (.read source)) :: rest) globals)
    (checked : resolve (before ++ .assign destination (.scalar (.read source)) :: rest) linked = .ok resolved)
    (sourceKnown : Visible globals source) (destinationKnown : Visible globals destination)
    {chain : Chain} {entries : Environment} (bound : entries source = some chain) {state : State}
    (layout : ModuleSlots globals state) (pool : LiveBindings globals resolved.program entries state) :
    ∃ next, Leaf.Step resolved globals before.length state (.assign destination (.scalar (.read source)))
      (.ok () next) ∧
      (ModuleSlots globals next ∧ LiveBindings globals resolved.program (entries.write destination (some chain)) next) ∧
      Bindings.Writes state destination next := by
  obtain ⟨_, _, _, _, address, _, code, live, installed, legal⟩ := pool source chain bound
  have related := global_operand sourceKnown
  obtain ⟨reads, tracked⟩ := RootCall.resolves_operand related
  have site := RootCall.checked_assign_site before rest destination _ _ reads globals linked resolved declared checked tracked
  have evaluated : RootCall.Evaluates state (.scalar (.read source)) (.ok (.function address) state) := by
    simpa [State.read, live.binding] using RootCall.Evaluates.name (state := state) source
  exact ⟨_, .setup site (.atom related evaluated), update_live layout pool (Preserves.refl state) (by
    intro other same
    cases same
    exact commit_live layout destinationKnown.1 code live.cell installed legal),
    .commit state (.function address) (Preserves.refl _)⟩

@[expose] def callResult : Chain → Option Chain
  | .wrapper _ _ child => some child
  | .mixed .. => none

theorem invoke_step {before after : List Command} {globals : List String} {name destination : String}
    {arguments : List Lowering.Resolve.SourceExpr} {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ invocation name destination arguments :: after) globals)
    (checked : resolve (before ++ invocation name destination arguments :: after) linked = .ok resolved)
    (callee : Visible globals name) (target : Visible globals destination)
    (allowed : ∀ arg ∈ arguments, Operand globals arg)
    {chain : Chain} {entries : Environment} (selected : entries name = some chain) {state : State}
    (layout : ModuleSlots globals state) (pool : LiveBindings globals resolved.program entries state) :
    ∃ out, Leaf.Step resolved globals before.length state (invocation name destination arguments) out ∧
      (∀ next, out = .ok () next →
        ModuleSlots globals next ∧
          LiveBindings globals resolved.program (entries.write destination (callResult chain)) next ∧
          Bindings.Writes state destination next) := by
  obtain ⟨_, seed, frame, rest, address, captures, code, live, installed, legal⟩ := pool name chain selected
  obtain ⟨links, keeps, outer, enclosing, same, profile, emits, scopes⟩ := code
  let continues (next : State) : Prop :=
    ModuleSlots globals next ∧ LiveBindings globals resolved.program (entries.write destination (callResult chain)) next ∧
      Bindings.Writes state destination next
  apply call_step declared checked callee allowed live (retained_head keeps) continues
  intro assigned
  cases chain with
  | mixed name parameters body =>
    obtain ⟨plan, lexical, planLegal, ownedLegal⟩ := leaf_plan profile same emits
    cases scopes with
    | mixed linkedLeaf =>
      obtain ⟨out, executed⟩ := leaf_total plan (activate state frame.declaration captures assigned)
      refine ⟨_, .leaf linkedLeaf lexical planLegal ownedLegal legal executed, fun value next result => ?_⟩
      have preserves := leaf_preserves state frame captures assigned plan executed value next result
      have ⟨valid, live⟩ := update_live (name := destination) (value := value) (shape := none)
        layout pool preserves (by intro _ impossible; cases impossible)
      exact ⟨valid, live, .commit next value preserves⟩
  | wrapper name parameters child =>
    cases profile with
    | wrapper paramsLegal childLegal childProfile =>
      cases links with
      | @wrapper _ _ _ _ childFrame frames childOwned wrapperCode childLinks =>
        cases emits with
        | @wrapper _ _ _ locals _ _ _ _ _ collect childEmits childSelection =>
          cases scopes with
          | wrapper childLexical =>
            have childCode : CallableCode globals resolved.program child seed childFrame frames :=
              ⟨childLinks, retained_tail keeps, _, _, child_scopes collect same, childProfile,
                childEmits, childLexical⟩
            obtain ⟨out, ran, result⟩ := child_total (name := name) (.wrapper collect childEmits childSelection)
              (.wrapper childOwned wrapperCode childLinks) keeps state layout target.1 captures installed legal
              (singleton_legal collect paramsLegal childLegal) assigned
            refine ⟨out, ran, fun value next returned => ?_⟩
            obtain ⟨_, ⟨slots, cells⟩, address, selected, liveChild, environment, childLegal⟩ := result value next returned
            have preserves := Preserves.of_old_cells slots cells
            have ⟨valid, live⟩ := update_live (name := destination) (value := value) (shape := some child)
              layout pool preserves (by
                intro other sameChild
                cases sameChild
                exact ⟨target.1, seed, childFrame, frames, address, selected, childCode, liveChild,
                  environment, childLegal⟩)
            exact ⟨valid, live, .commit next value preserves⟩


end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings
