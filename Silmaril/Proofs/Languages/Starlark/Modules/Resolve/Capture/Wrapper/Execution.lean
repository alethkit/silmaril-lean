module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (enter globalSlot fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper
open Silmaril.Languages.Starlark.Lists (Address Capture State Outcome Eval)
open Silmaril.Languages.Starlark.Functions

local notation "Value" => Silmaril.Languages.Starlark.Lists.Value
local notation "Flow" => Silmaril.Languages.Starlark.Lists.Iteration.Flow

private theorem head_found {seed program : Program} {frame : Frame} {rest : List Frame}
    (keeps : KeepsTable seed program (frame :: rest)) :
    program[(EmittedProgram seed rest).size]? = some frame.declaration :=
  keeps _ _ (by simp [EmittedProgram])

private theorem tail_kept {seed program : Program} {frame : Frame} {rest : List Frame}
    (keeps : KeepsTable seed program (frame :: rest)) : KeepsTable seed program rest := by
  intro index declaration found
  have within := (Array.getElem?_eq_some_iff.mp found).choose
  exact keeps index declaration (by simp [EmittedProgram, Array.getElem?_push, Nat.ne_of_lt within, found])

private theorem returns_child_exact (program : Program) (available : List DeclarationId)
    (active caller : State) (childName : String) (id : Nat) (child : Frame)
    (selected : List Capture) (address : Address) (previous : Option Value) (frozen : Bool)
    (found : program[id]? = some child.declaration) (addresses : Installs active child.free selected)
    (owner : active.slots (fileSlot childName) = some (.owned address))
    (cell : active.heap[address]? = some ⟨.binding previous, frozen⟩) :
    let next := installChild active childName id selected
    Exec program available active
        (.seq (.define (fileSlot childName) id) (.returnExpr (.atom (.read (.bound (fileSlot childName))))))
        (.ok (.returned (.function active.heap.size)) next) ∧
      ClosureAt (restoreCaller caller next) active.heap.size id child selected false := by
  let next := installChild active childName id selected
  have lookup : child.declaration.free.mapM (captureName active) = .ok selected :=
    installs_lookup active addresses
  have exactDefinition : define program (fileSlot childName) id [] active = .ok .next next := by
    simp only [define, found, lookup]
    simp [installChild, next, Frame.declaration, requiredSignature, Signature.defaulted, Signature.named,
      List.filterMap_map]
  obtain ⟨expected, ran, read, stored⟩ :=
    define_installs program child.declaration id (fileSlot childName) active caller address previous frozen
      selected found addresses owner cell
  have same : expected = next := by injection ran.symm.trans exactDefinition
  subst expected
  have defaults : defaultOperands program id = [] := by
    simp [defaultOperands, found, Frame.declaration, requiredSignature, Signature.defaulted, Signature.named,
      List.filterMap_map]
  have defined : Exec program available active (.define (fileSlot childName) id) (.ok .next next) := by
    have empty : ExecExprs program available active (defaultOperands program id) (.ok [] active) := by
      rw [defaults]
      exact .evaluatesMany (calls := fun _ _ _ => False) (fun _ _ _ h => h.elim) .empty
    have step := Exec.define (target := fileSlot childName) empty
    exact exactDefinition ▸ step
  have readback : Eval next (.read (.bound (fileSlot childName))) (.ok (.function active.heap.size) next) := by
    have same : next.read (.bound (fileSlot childName)) = .ok (.function active.heap.size) next := by
      simp [State.read, read]
    exact same ▸ Eval.read
  have returned : Exec program available next (.returnExpr (.atom (.read (.bound (fileSlot childName)))))
      (.ok (.returned (.function active.heap.size)) next) :=
    .returnExpr (.evaluates (calls := fun _ _ _ => False) (fun _ _ _ h => h.elim) (.atom trivial readback))
  exact ⟨.seq defined returned, ⟨stored, ⟨active, addresses⟩⟩⟩

private theorem reachable_child_addresses {globals : List String} {outer : List (List String)}
    {name : String} {params : List String} {child : Chain} {frame childFrame : Frame} {rest : List Frame}
    (emits : Emits globals outer (.wrapper name params child) (frame :: childFrame :: rest))
    (caller : State) (captures : List Capture) (assigned : List (Binding × Value))
    (environment : ∃ owner, Installs owner frame.free captures) :
    ∃ selected, Installs (activate caller frame.declaration captures assigned) childFrame.free selected := by
  have connected : Passes frame childFrame := (passes_along emits).rel
  have childScoped := scoped_frames emits childFrame (by simp)
  obtain ⟨owner, installed⟩ := environment
  exact child_installs frame childFrame owner caller captures assigned installed connected childScoped

theorem wrapper_total {seed : Program} {globals : List String} {outer : List (List String)}
    {name : String} {params : List String} {child : Chain} {frame childFrame : Frame} {rest : List Frame}
    (emits : Emits globals outer (.wrapper name params child) (frame :: childFrame :: rest))
    (caller : State) (captures : List Capture) (assigned : List (Binding × Value))
    (environment : ∃ owner, Installs owner frame.free captures) :
    ∃ selected, ReturnsChild seed caller child frame childFrame rest captures assigned selected
      (.ok (.function (activate caller frame.declaration captures assigned).heap.size)
        (restoreCaller caller (installChild (activate caller frame.declaration captures assigned)
          child.name (EmittedProgram seed rest).size selected))) := by
  obtain ⟨selected, addresses⟩ := reachable_child_addresses emits caller captures assigned environment
  exact ⟨selected, .returns addresses⟩

theorem wrapper_body {seed program : Program} {name : String} {params : List String}
    {caller : State} {child : Chain} {frame childFrame : Frame} {rest : List Frame}
    {captures selected : List Capture} {assigned : List (Binding × Value)}
    {nextAddress : Address} {next : State} (available : List DeclarationId)
    (links : Links seed (.wrapper name params child) (frame :: childFrame :: rest))
    (keeps : KeepsTable seed program (frame :: childFrame :: rest))
    (returns : ReturnsChild seed caller child frame childFrame rest captures assigned selected
      (.ok (.function nextAddress) next)) :
    let active := activate caller frame.declaration captures assigned
    ∃ final, Exec program available active frame.code (.ok (.returned (.function nextAddress)) final) ∧
      next = restoreCaller caller final ∧
      ClosureAt next nextAddress (EmittedProgram seed rest).size childFrame selected false := by
  cases links with
  | wrapper owned exactCode linkedChild =>
    cases returns with
    | returns addresses =>
      obtain ⟨destination, previous, frozen, slot, cell⟩ :=
        Entry.activated_cell caller frame captures assigned child.name owned
      have ⟨execute, closure⟩ := returns_child_exact program available _ caller child.name
        (EmittedProgram seed rest).size childFrame selected destination previous frozen
        (head_found (tail_kept keeps)) addresses slot cell
      exact ⟨_, exactCode ▸ execute, rfl, closure⟩

theorem checked_walk {seed : Program} {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command} {linked : Program}
    {resolved : ResolvedModule} {globals : List String} {outer : List (List String)} {state : State}
    {chain : Chain} {frame : Frame} {rest : List Frame} {address : Address} {captures : List Capture}
    {frozen : Bool} {operands : List (List Value)} {out : Outcome Value}
    (checked : resolve commands linked = .ok resolved)
    (emits : Emits globals outer chain (frame :: rest)) (links : Links seed chain (frame :: rest))
    (keeps : KeepsTable seed resolved.program (frame :: rest))
    (closure : ClosureAt state address (EmittedProgram seed rest).size frame captures frozen)
    (walk : Walk seed state chain (frame :: rest) address captures operands out) :
    NativeWalk resolved.program state address operands out := by
  generalize spine : frame :: rest = frames at walk
  induction walk generalizing outer frame rest frozen with
  | stop =>
    cases spine
    exact .stop closure.cell
  | arity binds =>
    cases spine
    have found := head_found keeps
    have admitted := List.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).choose
    exact .rejected (Entry.checked_prepare checked _ _ _ admitted _ _ _ _ _ _ closure.cell found binds)
  | step binds returns _ ih =>
    cases spine
    have found := head_found keeps
    have admitted := List.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).choose
    have prepared := Entry.checked_prepare checked _ _ _ admitted _ _ _ _ _ _ closure.cell found binds
    obtain ⟨final, ran, restored, childClosure⟩ :=
      wrapper_body (withoutDeclaration (List.range resolved.program.size) _) links keeps returns
    have leftover := tail_kept keeps
    cases links with
    | wrapper _ _ childLinks =>
      cases emits with
      | wrapper _ childEmits _ =>
        exact .returned prepared ran (restored ▸ ih childEmits childLinks leftover childClosure rfl)

theorem walk_total {seed program : Program} {globals : List String} {outer : List (List String)}
    {state : State} {chain : Chain} {frame : Frame} {rest : List Frame}
    {address : Address} {captures : List Capture} {frozen : Bool}
    (emits : Emits globals outer chain (frame :: rest)) (links : Links seed chain (frame :: rest))
    (keeps : KeepsTable seed program (frame :: rest))
    (closure : ClosureAt state address (EmittedProgram seed rest).size frame captures frozen)
    (operands : List (List Value)) (bounded : operands.length ≤ rest.length) :
    ∃ out, Walk seed state chain (frame :: rest) address captures operands out := by
  induction operands generalizing state chain outer frame rest address captures frozen with
  | nil => exact ⟨_, .stop⟩
  | cons values operands ih =>
    cases links with
    | mixed => simp at bounded
    | @wrapper name params child _ childFrame tail owned code childLinks =>
      have links : Links seed (.wrapper name params child) (frame :: childFrame :: tail) :=
        .wrapper owned code childLinks
      have bound : operands.length ≤ tail.length := Nat.le_of_succ_le_succ bounded
      obtain ⟨binding, boundArgs⟩ := Entry.binds_total frame.parameters values
      cases binding with
      | error error => exact ⟨_, .arity boundArgs⟩
      | ok assigned =>
        obtain ⟨selected, returned⟩ := wrapper_total (seed := seed) emits state captures assigned closure.environment
        obtain ⟨_, _, _, escaped⟩ := wrapper_body [] links keeps returned
        have childKept := tail_kept keeps
        cases emits with
        | wrapper _ childEmits _ =>
          obtain ⟨out, reached⟩ := ih childEmits childLinks childKept escaped bound
          exact ⟨out, .step boundArgs returned reached⟩

theorem native_walk_denotes {program : Program} {state : State} {address : Address}
    {operands : List (List Value)} {out : Outcome Value}
    (native : NativeWalk program state address operands out) :
    denoteWalk program operands (.function address) state = out := by
  induction native with
  | stop => rfl
  | rejected prepare =>
    rw [denoteWalk]
    dsimp only
    simp [Lowering.denoteDispatchWith, prepare, Outcome.resume]
  | returned prepare ran _ ih =>
    have denoted := (exec_iff_denoteBody _ _ _ _ _).mp ran
    rw [denoteWalk]
    dsimp only
    simpa [Lowering.denoteDispatchWith, prepare, denoted, Outcome.resume, Lowering.callValue] using ih

theorem checked_root_object (after : List Command) (chain : Chain) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (.define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (.define chain.name (.required chain.parameters) chain.body :: after) linked = .ok resolved)
    (accepted : ∀ program, Accepted globals program [] chain)
    (suffix : RootCall.Segment globals after) (caller : State) :
    let initial := enter resolved.source caller
    ∃ seed head rest next captures, Emits globals [] chain (head :: rest) ∧ Links seed chain (head :: rest) ∧
      KeepsTable seed resolved.program (head :: rest) ∧
      resolved.source.commands[0]? = some (.exec (.define chain.name (EmittedProgram seed rest).size)) ∧
      Exec resolved.program (List.range resolved.program.size) initial
        (.define (globalSlot chain.name) (EmittedProgram seed rest).size) (.ok .next next) ∧
      next.bindingValue (globalSlot chain.name) = .ok (.function initial.heap.size) ∧
      ClosureAt next initial.heap.size (EmittedProgram seed rest).size head captures false := by
  obtain ⟨seed, head, rest, emits, links, command, keeps⟩ :=
    RootCall.checked_chain_site [] after chain globals linked resolved binders checked accepted suffix
  obtain ⟨next, captures, installed, ran, binding, stored⟩ :=
    Entry.checked_root_definition binders checked emits List.mem_cons_self caller _ (head_found keeps)
  exact ⟨seed, head, rest, next, captures, emits, links, keeps, command,
    (exec_iff_denoteBody _ _ _ _ _).mpr ran, binding, ⟨stored, ⟨_, installed⟩⟩⟩

private theorem chain_length {seed : Program} {chain : Chain} {frames : List Frame}
    (links : Links seed chain frames) : frames.length = wrapperCount chain + 1 := by
  induction links with
  | mixed => rfl
  | wrapper _ _ _ ih => simpa [wrapperCount, Nat.add_assoc] using (Nat.add_right_cancel ih)

theorem checked_root_walk (after : List Command) (chain : Chain) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (.define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (.define chain.name (.required chain.parameters) chain.body :: after) linked = .ok resolved)
    (accepted : ∀ program, Accepted globals program [] chain)
    (suffix : RootCall.Segment globals after) (caller : State)
    (operands : List (List Value)) (bounded : operands.length ≤ wrapperCount chain) :
    let initial := enter resolved.source caller
    ∃ seed head rest next captures out,
      resolved.source.commands[0]? = some (.exec (.define chain.name (EmittedProgram seed rest).size)) ∧
      Exec resolved.program (List.range resolved.program.size) initial
        (.define (globalSlot chain.name) (EmittedProgram seed rest).size) (.ok .next next) ∧
      Walk seed next chain (head :: rest) initial.heap.size captures operands out ∧
      NativeWalk resolved.program next initial.heap.size operands out ∧
      denoteWalk resolved.program operands (.function initial.heap.size) next = out := by
  obtain ⟨seed, head, rest, next, captures, emits, links, keeps, site, root, _, closure⟩ :=
    checked_root_object after chain globals linked resolved binders checked accepted suffix caller
  have length : rest.length = wrapperCount chain := Nat.add_right_cancel (chain_length links)
  obtain ⟨out, walked⟩ := walk_total emits links keeps closure operands (length.symm ▸ bounded)
  have runs := checked_walk checked emits links keeps closure walked
  exact ⟨seed, head, rest, next, captures, out, site, root, walked, runs, native_walk_denotes runs⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper
