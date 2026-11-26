module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (enter fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (ClosureAt)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named (resolves_at runs_at)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (resolveTracked)
open Silmaril.Languages.Starlark.Lists (State Slot Outcome)
open Silmaril.Languages.Starlark.Modules.Loader (Session)

local notation "Value" => Lists.Value

theorem consumer_layout (plan : Consumer) {program : Program} {consumer : ResolvedModule}
    (checked : resolve plan.commands program = .ok consumer) :
    consumer.program = program ∧ consumer.source.commands = plan.code ∧
    consumer.source.globals = [plan.destination, plan.tail] ∧ consumer.source.fileNames = [plan.alias] := by
  let lexical := block plan.alias plan.destination plan.tail
  have callee : Body.Operand lexical (.scalar (.read plan.alias))
      (Leaf.readOperand (fileSlot plan.alias)) [fileSlot plan.alias] :=
    .read plan.legal (.owned (by simp [lexical, block])) (.owned (by simp [lexical, block]))
  have call := resolves_at (fileSlot plan.alias) callee plan.operands plan.keywords plan.star plan.mapping
  have context : moduleBlock plan.commands = ⟨lexical.context, .global⟩ := by
    simp [moduleBlock, fileNames, globalNames, Consumer.commands, Consumer.item, lexical, block,
      Assignment.LexicalBlock.context]
  have first := elaborateCommand_assign ⟨lexical.context, .global⟩ plan.destination plan.call program
  have tail := elaborateCommand_assign ⟨lexical.context, .global⟩ plan.tail plan.rhs program
  have resolvedRhs : resolveTracked lexical.context plan.rhs = .ok (plan.rhsCode, plan.rhsReads) := by
    have operand : Lowering.Resolve.resolveExpr lexical.context plan.rhs [] =
        .ok (plan.rhsCode, plan.rhsReads.reverse) := by
      simpa [lexical] using Body.resolves_at plan.suffix []
    simp [resolveTracked, operand, Except.map]
  rw [show resolveTracked lexical.context plan.call = .ok (_, _) from call] at first
  rw [resolvedRhs] at tail
  have compiled : elaborateCommands plan.commands program = .ok (plan.code, program) := by
    rw [elaborateCommands, context]
    have load : elaborateCommand ⟨lexical.context, .global⟩ (.load plan.label [plan.item]) program =
        .ok (.load plan.label [plan.item], program) := elaborateCommand_load _ _ _ _ _
    simp [Consumer.commands, Consumer.code, List.mapM_cons, bind, StateT.bind, Except.bind, pure,
      StateT.pure, Except.pure, load, first, tail, Except.map, Except.mapError, Consumer.callCode]
  have detail := checked_of_resolve checked
  obtain ⟨sameCode, sameTable⟩ := Prod.mk.inj (Except.ok.inj (detail.1.symm.trans compiled))
  refine ⟨sameTable, sameCode, ?_, ?_⟩
  · simpa [Consumer.commands, globalNames] using detail.2.1
  · simp [Modules.Source.fileNames, detail.2.2.1, sameCode, Consumer.code, Consumer.item]

theorem import_agrees {plan : Consumer} {published : Modules.Published} {s : State} {out : Modules.Result Unit}
    (source : BindsAlias plan published s out) :
    Modules.bindImports (Modules.importsOf published plan.label [plan.item]) s = out := by
  cases source with
  | missing absent =>
    simp [Modules.importsOf, Modules.bindImports, Consumer.item, plan.publicName, absent, List.mapM_cons,
      bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
  | found loaded =>
    simp [Modules.importsOf, Modules.bindImports, Consumer.item, plan.publicName, loaded, List.mapM_cons,
      bind, Except.bind, pure, Except.pure]

/-- Read the actual imported file-local slot and keep the record at the
published address. The import writes one owned binding cell. -/
theorem reached_alias {plan : Consumer} {callee : Callable} {before defining : State}
    {address aliasCell : Nat} {frozen : Bool}
    (owned : before.slots (fileSlot plan.alias) = some (.owned aliasCell))
    (blank : before.heap[aliasCell]? = some ⟨.binding none, frozen⟩)
    (record : ClosureAt callee.site callee.id defining before address) :
    let bound := before.write (fileSlot plan.alias) (.function address)
    Body.Evaluates (block plan.alias plan.destination plan.tail) bound (.scalar (.read plan.alias))
      (Leaf.readOperand (fileSlot plan.alias)) (.ok (.function address) bound) ∧
    Nonempty (ClosureAt callee.site callee.id defining bound address) := by
  intro bound
  have within := (Array.getElem?_eq_some_iff.mp blank).choose
  have loaded : bound.bindingValue (fileSlot plan.alias) = .ok (.function address) := by
    simp [bound, State.bindingValue, Slot.address, State.write, owned, blank,
      Array.getElem?_setIfInBounds_self_of_lt within]
  have read := Body.Evaluates.read (state := bound)
    (Assignment.ReadResolves.owned (block := block plan.alias plan.destination plan.tail)
      (name := plan.alias) (by simp [block]))
  change Body.Evaluates _ _ _ _ (bound.read (.bound (fileSlot plan.alias))) at read
  rw [State.read, loaded] at read
  refine ⟨read, ⟨{record with recorded := ?_, live := Body.capture_cells_written _ _ _ record.live}⟩⟩
  have different : before.slots (fileSlot plan.alias) ≠ some (.owned address) := by
    intro hit
    have same : aliasCell = address := by simpa [owned] using hit
    subst aliasCell
    rw [record.recorded] at blank
    cases blank
  exact (RootCall.write_other_cell _ _ _ _ different).trans record.recorded

private theorem assigned_step {program : Program} {manifest : Modules.Loader.Manifest} {active : List Nat}
    {s : Session} {id : Nat} {name : String} {code : Lowering.Expr} {out : Outcome Value}
    (exec : ExecExpr program (List.range program.size) s.runtime code out) :
    Modules.Loader.Runs program manifest active (.command id (.exec (.assignExpr name code))) s
      (Modules.Loader.liftResult id s (afterWrite name out)) := by
  cases out <;> exact .exec (code := .assignExpr name code) (.assignExpr exec)

theorem tail_reached {program : Program} {manifest : Modules.Loader.Manifest} {consumer : ResolvedModule}
    {plan : Consumer} (checked : resolve plan.commands program = .ok consumer)
    (same : consumer.program = program) (callee : Callable) (linked : callee.Linked program)
    {s : Session} {defining : State} {address : Nat}
    (read : Body.Evaluates (block plan.alias plan.destination plan.tail) s.runtime
      (.scalar (.read plan.alias)) (Leaf.readOperand (fileSlot plan.alias)) (.ok (.function address) s.runtime))
    (closure : ClosureAt callee.site callee.id defining s.runtime address) :
    ∃ out, Tail plan callee s.runtime out ∧
      Modules.Loader.Runs program manifest [1] (.commands 1 plan.code.tail) s
        (Modules.Loader.liftResult 1 s out) := by
  have linkedHere : callee.Linked consumer.program := same.symm ▸ linked
  have found := linkedHere.1
  have permitted : callee.id ∈ List.range consumer.program.size :=
    List.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).choose
  obtain ⟨result, source, native, _, _⟩ :=
    runs_at callee.site callee.BodyRuns checked callee.id found _ permitted
      (enter_callable checked linkedHere) (fileSlot plan.alias) read closure
      plan.operands plan.keywords plan.star plan.mapping
  have exactCall : ExecExpr program (List.range program.size) s.runtime plan.callCode result := same ▸ native
  have step := assigned_step (manifest := manifest) (id := 1) (active := [1])
    (s := s) (name := plan.destination) exactCall
  cases result with
  | error error stopped =>
    exact ⟨_, .callError source, .failed step⟩
  | ok value returned =>
    let next := returned.write (globalSlot plan.destination) value
    obtain ⟨suffix, evaluated, _⟩ := Body.operand_total plan.suffix next
    have nativeSuffix : ExecExpr program (List.range program.size) next plan.rhsCode suffix :=
      .evaluates (calls := fun _ _ _ => False) (fun _ _ _ no => no.elim)
        (Body.evaluates_with _ _ _ evaluated)
    have tail := assigned_step (manifest := manifest) (id := 1) (active := [1])
      (s := {s with runtime := next}) (name := plan.tail) nativeSuffix
    refine ⟨_, .called source evaluated, .step step ?_⟩
    cases suffix with
    | error => exact .failed tail
    | ok => exact .step tail .done

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
