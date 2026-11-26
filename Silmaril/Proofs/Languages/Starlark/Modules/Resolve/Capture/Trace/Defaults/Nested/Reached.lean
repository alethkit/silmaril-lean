module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Run

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome Capture Cell)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow)

theorem plan_of_body {parent : LexicalBlock} {source : Defaults.Body.Definition}
    (target : source.name ∈ parent.owned) {locals : List String}
    (binders : Block.LocalBinders source.parameters.names source.body.binders locals)
    {code : Body} {reads : List Binding}
    (body : Defaults.Body.Elaborates ⟨source.parameters.names ++ locals, parent.owned ++ parent.enclosing,
      parent.globals⟩ source.body code reads)
    {items : List PlainPositionalDefault} (defaults : Defaults.Lexical.Elaborates parent source.parameters.optional items) :
    Nonempty (Plan parent source) := by
  obtain ⟨bodyPlan⟩ := Defaults.Body.plan_in_scope parent.globals source locals _ binders body
  exact ⟨⟨target, bodyPlan, items, defaults⟩⟩

theorem compile_definition {parent : LexicalBlock} {source : Defaults.Body.Definition}
    (plan : Plan parent source) (seed : Program) :
    compileBody ⟨parent.context, .local⟩ (statement source) seed =
      .ok (⟨.define (fileSlot source.name) seed.size, plan.reads⟩, seed.push plan.declaration) := by
  obtain ⟨same, tracked⟩ := Defaults.Lexical.translates plan.lexical
  exact Defaults.Body.compile_nested plan.body plan.defaults same tracked seed

private theorem default_origins {parent : LexicalBlock} {source : List (String × Lowering.Resolve.SourceExpr)}
    {items : List PlainPositionalDefault} (defaults : Defaults.Lexical.Elaborates parent source items) :
    ∀ binding ∈ items.flatMap PlainPositionalDefault.reads, ∃ origin, ReadOrigin parent binding origin := by
  induction defaults with
  | nil => simp
  | cons operand _ ih =>
    intro binding member
    rcases List.mem_append.mp member with first | rest
    · exact Defaults.Body.operand_origins operand binding first
    · exact ih binding rest

theorem read_origins {parent : LexicalBlock} {source : Defaults.Body.Definition} (plan : Plan parent source) :
    ∀ binding ∈ plan.reads, ∃ origin, ReadOrigin parent binding origin := by
  intro binding member
  rcases List.mem_append.mp member with readDefault | captured
  · exact default_origins plan.lexical binding readDefault
  · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp captured
    obtain ⟨binding, rfl, origin⟩ := selected_origin plan.body.selects entry present
    rcases origin with localName | moduleName
    · cases localName with
      | @enclosing name _ visible =>
        rcases List.mem_append.mp visible with owned | inherited
        · exact ⟨.owned, .owned owned⟩
        · by_cases owned : name ∈ parent.owned
          · exact ⟨.owned, .owned owned⟩
          · exact ⟨.enclosing, .enclosing owned inherited⟩
    · cases moduleName with
      | module _ missing declared =>
        exact ⟨.module, .module (fun own => missing (List.mem_append_left _ own))
          (fun outer => missing (List.mem_append_right _ outer)) declared⟩

theorem selects_parent {parent : LexicalBlock} {source : Defaults.Body.Definition} (plan : Plan parent source)
    {before after : List Binding}
    (surrounding : ∀ binding ∈ before ++ after, ∃ origin, ReadOrigin parent binding origin) :
    ∃ free, Selects parent (before ++ plan.reads ++ after) free := by
  apply selects_of_origins
  intro binding member
  rcases List.mem_append.mp member with earlier | later
  · rcases List.mem_append.mp earlier with beforeSite | atSite
    · exact surrounding binding (List.mem_append_left _ beforeSite)
    · exact read_origins plan binding atSite
  · exact surrounding binding (List.mem_append_right _ later)

private theorem capture_vector {state : State} (free : List FreeName)
    (supplied : ∀ entry ∈ free, ∃ capture, ReceivesAddress state entry capture ∧
      ∃ value frozen, state.heap[capture.address]? = some ⟨.binding value, frozen⟩) :
    ∃ captures, Installs state free captures ∧ Defaults.Body.CaptureCells state captures := by
  induction free with
  | nil => exact ⟨[], .nil, by simp [Defaults.Body.CaptureCells]⟩
  | cons first rest ih =>
    obtain ⟨head, received, live⟩ := supplied first List.mem_cons_self
    obtain ⟨tail, installed, cells⟩ := ih (fun entry member => supplied entry (List.mem_cons_of_mem _ member))
    refine ⟨head :: tail, .cons received installed, ?_⟩
    intro capture present
    rcases List.mem_cons.mp present with rfl | later
    · exact live
    · exact cells _ later

private theorem demand {parent : LexicalBlock} {source : Defaults.Body.Definition}
    (plan : Plan parent source) {before after : List Binding} {parentFree : List FreeName}
    (selected : Selects parent (before ++ plan.reads ++ after) parentFree)
    {binding : Binding} (requested : (⟨binding, binding⟩ : FreeName) ∈ plan.body.free)
    (outside : binding.scope = .global ∨ binding.name ∉ parent.owned) :
    (⟨binding, binding⟩ : FreeName) ∈ parentFree := by
  have seen : binding ∈ plan.reads := List.mem_append_right _ (List.mem_map.mpr ⟨_, requested, rfl⟩)
  exact (selected_member selected binding).mpr ⟨by simp only [List.mem_append, seen, or_true, true_or], outside⟩

theorem installs {parent : LexicalBlock} {source : Defaults.Body.Definition}
    (plan : Plan parent source) {before after : List Binding} {parentFree : List FreeName}
    (selected : Selects parent (before ++ plan.reads ++ after) parentFree)
    {state : State} {floor : Nat} (frame : Defaults.Body.Frame parent parentFree floor state) :
    ∃ captures, Installs state plan.body.free captures ∧ Defaults.Body.CaptureCells state captures := by
  apply capture_vector
  intro entry member
  obtain ⟨binding, rfl, origin⟩ := selected_origin plan.body.selects entry member
  rcases origin with localName | moduleName
  · cases localName with
    | @enclosing name _ _ =>
      by_cases owned : name ∈ parent.owned
      · obtain ⟨address, value, frozen, _, slot, cell⟩ := frame.owned name owned
        exact ⟨⟨fileSlot name, address, true⟩, .enclosing slot, value, frozen, cell⟩
      · obtain ⟨address, value, frozen, _, slot, cell⟩ :=
          frame.captured (fileSlot name) (demand plan selected member (.inr owned))
        exact ⟨⟨fileSlot name, address, true⟩, .forwardedLocal slot, value, frozen, cell⟩
  · cases moduleName with
    | @module name _ _ _ =>
      obtain ⟨address, value, frozen, _, slot, cell⟩ :=
        frame.captured (globalSlot name) (demand plan selected member (.inl rfl))
      exact ⟨⟨globalSlot name, address, false⟩, .capturedGlobal slot, value, frozen, cell⟩

theorem activate_forwarded {parent : LexicalBlock} {source : Defaults.Body.Definition} (plan : Plan parent source)
    {state : State} {captures : List Capture} (installed : Installs state plan.body.free captures)
    (caller : State) (assigned : List (Binding × Silmaril.Languages.Starlark.Lists.Value)) (name : String) (address : Nat)
    (present : (⟨fileSlot name, fileSlot name⟩ : FreeName) ∈ plan.body.free)
    (forwarded : state.slots (fileSlot name) = some (.captured address true)) :
    (activate caller plan.declaration captures assigned).slots (fileSlot name) =
      some (.captured address true) := by
  obtain ⟨capture, found, _, receipt⟩ := Forwarding.find_receipt installed (fileSlot name) present
  have captured : capture = ⟨fileSlot name, address, true⟩ := by
    cases receipt with
    | enclosing owned => simp [forwarded] at owned
    | forwardedLocal slot =>
      have equal := Option.some.inj (forwarded.symm.trans slot)
      cases equal
      rfl
  have slots : plan.declaration.signature.slots ++ plan.declaration.locals = plan.body.block.owned.map fileSlot := by
    apply Defaults.Body.declaration_slots
    have identified := (Defaults.Lexical.translates plan.lexical).1
    simpa using congrArg List.length identified
  have external : fileSlot name ∉ plan.declaration.signature.slots ++ plan.declaration.locals := by
    rw [slots]
    rintro member
    obtain ⟨ownedName, owned, equal⟩ := List.mem_map.mp member
    exact selected_outside_owned plan.body.selects _ present ownedName owned equal.symm
  subst capture
  exact activate_capture caller plan.declaration captures ⟨fileSlot name, address, true⟩ assigned found external

private theorem installed_record {parent : LexicalBlock} {source : Defaults.Body.Definition}
    (plan : Plan parent source) {state final : State} {floor : Nat} {parentFree : List FreeName}
    (frame : Defaults.Body.Frame parent parentFree floor state) {values : List Silmaril.Languages.Starlark.Lists.Value}
    (evaluated : Defaults.Lexical.Evaluates parent state plan.defaults (.ok values final))
    (id : DeclarationId) (captures : List Capture) :
    DefinitionResult plan id captures state
      (.ok .next (Defaults.install (fileSlot source.name) id captures
        ((source.parameters.optional.map (fileSlot ∘ Prod.fst)).zip values) final)) := by
  have kept := Defaults.Lexical.evaluates_keeps plan.lexical evaluated
  obtain ⟨target, before, frozen, _, slot, cell⟩ := frame.owned source.name plan.target
  have targetSlot : final.slots (fileSlot source.name) = some (.owned target) := kept.1 ▸ slot
  have oldBound := (Array.getElem?_eq_some_iff.mp cell).choose
  have targetCell : final.heap[target]? = some ⟨.binding before, frozen⟩ := kept.2 _ _ oldBound cell
  have finalBound : target < final.heap.size := (Array.getElem?_eq_some_iff.mp targetCell).choose
  let name := fileSlot source.name
  let record := (source.parameters.optional.map (fileSlot ∘ Prod.fst)).zip values
  let grown := { final with heap := final.heap.push (⟨.function ⟨id, captures, record⟩, false⟩ : Cell) }
  have grownCell : grown.heap[target]? = some ⟨.binding before, frozen⟩ :=
    by simpa [grown, Array.getElem?_push, Nat.ne_of_lt finalBound] using targetCell
  have written : (grown.write name (.function final.heap.size)).bindingValue name =
      .ok (.function final.heap.size) := by
    have valid : target < grown.heap.size := (Array.getElem?_eq_some_iff.mp grownCell).choose
    simp only [State.write, show grown.slots name = some (.owned target) from targetSlot, grownCell,
      State.bindingValue, Silmaril.Languages.Starlark.Lists.Slot.address,
      Array.getElem?_setIfInBounds_self_of_lt valid]
  have stored : (grown.write name (.function final.heap.size)).heap[final.heap.size]? =
      some ⟨.function ⟨id, captures, record⟩, false⟩ := by
    simp only [State.write, show grown.slots name = some (.owned target) from targetSlot, grownCell]
    exact (Array.getElem?_setIfInBounds_ne (Nat.ne_of_lt finalBound)).trans Array.getElem?_push_size
  exact .installed evaluated rfl written stored

theorem result_frame {parent : LexicalBlock} {source : Defaults.Body.Definition}
    (plan : Plan parent source) {id : DeclarationId} {captures : List Capture}
    {state : State} {free : List FreeName} {floor : Nat} (frame : Defaults.Body.Frame parent free floor state)
    {out : Outcome Flow} (result : DefinitionResult plan id captures state out) :
    Defaults.Body.Frame parent free floor (Silmaril.Languages.Starlark.Lists.Iteration.finishState out) ∧
      Defaults.Body.Keeps floor state (Silmaril.Languages.Starlark.Lists.Iteration.finishState out) := by
  have extendsHeap {next : State} (preserved : Defaults.Body.Keeps state.heap.size state next) :
      Defaults.Body.Extends state next :=
    ⟨preserved.1, fun address cell found => preserved.2 address cell (Array.getElem?_eq_some_iff.mp found).choose found⟩
  cases result with
  | failed _ kept =>
    exact ⟨Defaults.Body.extend_frame frame (extendsHeap kept), Defaults.Body.extends_keeps floor (extendsHeap kept)⟩
  | @installed values next evaluated ran exactState _ _ =>
    subst next
    have kept := extendsHeap (Defaults.Lexical.evaluates_keeps plan.lexical ran)
    have before := Defaults.Body.extend_frame frame kept
    have grown := Defaults.Body.extend_push evaluated
      ⟨.function ⟨id, captures, (source.parameters.optional.map (fileSlot ∘ Prod.fst)).zip values⟩, false⟩
    have after := Defaults.Body.extend_frame before grown
    obtain ⟨written, retained⟩ := Defaults.Body.written_frame plan.target (.function evaluated.heap.size) after
    exact ⟨written, Defaults.Body.keeps_trans (Defaults.Body.extends_keeps floor kept)
      (Defaults.Body.keeps_trans (Defaults.Body.extends_keeps floor grown) retained)⟩

theorem reached {parent : LexicalBlock} {source : Defaults.Body.Definition} (plan : Plan parent source)
    {before after : List Binding} {parentFree : List FreeName}
    (selected : Selects parent (before ++ plan.reads ++ after) parentFree)
    (program : Program) (available : List DeclarationId) (id : DeclarationId)
    (found : program[id]? = some plan.declaration) {state : State} {floor : Nat}
    (frame : Defaults.Body.Frame parent parentFree floor state) :
    ∃ captures out, Installs state plan.body.free captures ∧ Defaults.Body.CaptureCells state captures ∧
      Defaults.Lexical.Defines parent (fileSlot source.name) id plan.body.free source.parameters plan.defaults state out ∧
      Exec program available state (.define (fileSlot source.name) id) out ∧
      denoteBody program available (.define (fileSlot source.name) id) state = out ∧
      DefinitionResult plan id captures state out := by
  obtain ⟨captures, supplied, cells⟩ := installs plan selected frame
  obtain ⟨out, sourceStep, ran, meaning, saved⟩ := Defaults.Lexical.defines_total program available
    (fileSlot source.name) id source.parameters plan.declaration plan.lexical found rfl state captures supplied
  refine ⟨captures, out, supplied, cells, sourceStep, ran, meaning, ?_⟩
  cases sourceStep with
  | failed evaluated => exact .failed evaluated (Defaults.Lexical.evaluates_keeps plan.lexical evaluated)
  | @installed final values actual evaluated used =>
    obtain ⟨reached, savedValues, savedEvaluation, equal⟩ := saved _ rfl
    rw [equal]
    exact installed_record plan frame savedEvaluation id captures

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested
