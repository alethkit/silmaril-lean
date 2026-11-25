module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry

open Execution
open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Context.Resume (Continuation)

/-- The allocated function starts with initial operands and a designated site
after a numeric prefix. The site may be in a parameterless scalar block.
The declaration and continuation targets belong to the registered graph function. -/
structure Entry where
  cont : Continuation
  op : Source.Op
  before : List Prefix.Op := []

def Entry.siteBody (entry : Entry) : Source.Body := .indirect entry.before entry.op entry.cont.code

def Entry.body (entry : Entry) : Source.Body :=
  match entry.cont.block with
  | none => entry.siteBody
  | some block => .block block.result entry.siteBody block.tail

def Entry.initial (entry : Entry) : List Value :=
  match entry.cont.block with
  | none => entry.cont.owner.initial
  | some _ => []

def Entry.check (entry : Entry) (program : Graph.Program) (tables : Source.Tables) : Bool :=
  let fn := entry.cont.owner
  program.checkDirect && entry.body.checkRegion program tables fn fn.declaration.results [] (Prefix.stackTypes fn.initial)

def Entry.frame (entry : Entry) (args : List Value) : Frame :=
  entry.cont.owner.declaration.frame args

/-- The remaining numeric instructions and the current operand stack. -/
abbrev OperandState := List Value × List Prefix.Op

inductive OperandResult where
  | values (stack : List Value)
  | trap (saved : List Value) (rest : List Prefix.Op)

/-- A finite list of the states before each numeric step. The last
reduction either hands the finished stack to lookup or raises a trap. -/
inductive OperandTrace (locals : List Value) :
    List Value → List Prefix.Op → List OperandState → OperandResult → Prop where
  | done (stack) : OperandTrace locals stack [] [] (.values stack)
  | value {stack op rest next states result}
      (move : Prefix.Reduce locals stack op (.values next))
      (tail : OperandTrace locals next rest states result) :
      OperandTrace locals stack (op :: rest) ((stack, op :: rest) :: states) result
  | trap {stack op rest saved} (move : Prefix.Reduce locals stack op (.trap saved)) :
      OperandTrace locals stack (op :: rest) [(stack, op :: rest)] (.trap saved rest)

abbrev Entry.OperandTrace (entry : Entry) (args : List Value) :=
  GraphEntry.OperandTrace (entry.frame args).locals entry.initial entry.before

def Entry.prepare (entry : Entry) (program : Graph.Program) (tables : Source.Tables) (args : List Value)
    (stack : List Value) : Option Source.Activation :=
  if args.map Value.type = entry.cont.owner.declaration.params then
    entry.op.prepare program tables (entry.frame args) stack
  else none

structure Entry.Checked (entry : Entry) (program : Graph.Program) (tables : Source.Tables)
    (outer : Frame) (index : FuncIdx) (args : List Value) : Prop where
  source : entry.check program tables = true
  found : program.lookup entry.cont.address = some entry.cont.owner
  resolves : outer.module.funcs[index.toNat]? = some entry.cont.address
  typed : args.map Value.type = entry.cont.owner.declaration.params

structure Entry.AtSite (entry : Entry) (program : Graph.Program) (tables : Source.Tables)
    (outer : Frame) (index : FuncIdx) (args : List Value) (states : List OperandState)
    (stack : List Value) (active : Source.Activation) : Prop where
  checked : entry.Checked program tables outer index args
  trace : entry.OperandTrace args states (.values stack)
  prepared : entry.prepare program tables args stack = some active

def Entry.coreFunc (entry : Entry) : Wasm.Func :=
  let fn := entry.cont.owner
  { fn.coreFunc with body := fn.initial.map Graph.coreCodeSyntax.ops.value ++ entry.body.core }

def Entry.limeFunc (entry : Entry) : Wasm.Lime1.Func :=
  let fn := entry.cont.owner
  { fn.limeFunc with body := fn.initial.map Graph.limeCodeSyntax.ops.value ++ entry.body.lime }

def Entry.coreInstance {H : Type} (entry : Entry) : Core.FuncInst H :=
  let decl := entry.cont.owner.declaration
  ⟨decl.type.toDefType, decl.module.toCore, .wasm entry.coreFunc⟩

def Entry.limeInstance {H : Type} (entry : Entry) : Runtime.FuncInst Wasm.Lime1.Func H :=
  let decl := entry.cont.owner.declaration
  .wasm decl.type decl.module entry.limeFunc

/-- The entry is allocated with the actual indirect source body. The linked
direct targets and the table entries retain their exact direct graph bodies. -/
structure Entry.CoreAllocated {H : Type} (entry : Entry) (program : Graph.Program) (tables : Source.Tables)
    (active : Source.Activation) (s : Core.Store H) : Prop where
  entry : s.funcs[entry.cont.address.value]? = some entry.coreInstance
  links : program.CoreLinksAllocated s
  tables : Source.Tables.CoreAllocated tables s
  targets : active.binding.site.CoreAllocated program s

structure Entry.LimeAllocated {H : Type} (entry : Entry) (program : Graph.Program) (tables : Source.Tables)
    (active : Source.Activation) (s : Wasm.Lime1.Execution.Store H) : Prop where
  entry : s.funcs[entry.cont.address.value]? = some entry.limeInstance
  links : program.LimeLinksAllocated s
  tables : Source.Tables.LimeAllocated tables s
  targets : active.binding.site.LimeAllocated program s

def coreSource {H : Type} (s : Core.Store H) (outer : Frame) (index : FuncIdx) (args : List Value) :
    Core.Config H :=
  ⟨s, outer.toCore, coreValues args ++ [.plain (.call index)]⟩

def Entry.coreInvoke {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame) (args : List Value) :
    Core.Config H :=
  ⟨s, outer.toCore, coreValues args ++
    [.ref (.func entry.cont.address.value), .callRefType entry.cont.owner.declaration.type.toDefType]⟩

/-- The function label immediately after native invocation. -/
def Entry.coreBody {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame) (args : List Value) :
    Core.Config H :=
  entry.cont.coreWrap outer ⟨s, (entry.frame args).toCore, Core.expression entry.coreFunc.body⟩

def Entry.coreSiteCode (entry : Entry) (remaining : List Prefix.Op) : List Core.Admin :=
  remaining.map (Prefix.emit coreSyntax) ++ .plain entry.op.coreInstr :: entry.cont.code.map Graph.coreEmit

def Entry.coreOperands {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame)
    (args : List Value) (state : OperandState) : Core.Config H :=
  entry.cont.coreSiteWrap outer ⟨s, (entry.frame args).toCore, coreValues state.1 ++ entry.coreSiteCode state.2⟩

def Entry.coreBefore {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame) (index : FuncIdx)
    (args : List Value) (states : List OperandState) : List (Core.Config H) :=
  coreSource s outer index args :: entry.coreInvoke s outer args ::
    (entry.cont.block.toList.map (fun _ => entry.coreBody s outer args) ++ states.map (entry.coreOperands s outer args))

def Entry.coreLookup {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame)
    (active : Source.Activation) (phase : Indirect.Phase) : Core.Config H :=
  entry.cont.coreWrap outer (active.coreConfig s entry.cont.scopes entry.cont.code phase)

def Entry.corePrefix {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame) (index : FuncIdx)
    (args : List Value) (active : Source.Activation) (out : Outcome) (states : List OperandState) :
    List (Core.Config H) :=
  entry.coreBefore s outer index args states ++
    out.coreTrace.map (entry.coreLookup s outer active)

open Wasm.Lime1.Execution in
def limeSource {H : Type} (s : Store H) (outer : Frame) (index : FuncIdx) (args : List Value) : Config H :=
  ⟨s, outer, values args ++ [.source (.call index)]⟩

open Wasm.Lime1.Execution in
def Entry.limeInvoke {H : Type} (entry : Entry) (s : Store H) (outer : Frame) (args : List Value) : Config H :=
  ⟨s, outer, values args ++ [.invoke entry.cont.address]⟩

open Wasm.Lime1.Execution in
/-- The function label immediately after native invocation. -/
def Entry.limeBody {H : Type} (entry : Entry) (s : Store H) (outer : Frame) (args : List Value) : Config H :=
  entry.cont.limeWrap outer ⟨s, entry.frame args, expression entry.limeFunc.body⟩

open Wasm.Lime1.Execution in
def Entry.limeSiteCode (entry : Entry) (remaining : List Prefix.Op) : List Admin :=
  remaining.map (Prefix.emit limeSyntax) ++ .source entry.op.limeInstr :: entry.cont.code.map Graph.limeEmit

open Wasm.Lime1.Execution in
def Entry.limeOperands {H : Type} (entry : Entry) (s : Store H) (outer : Frame)
    (args : List Value) (state : OperandState) : Config H :=
  entry.cont.limeSiteWrap outer ⟨s, entry.frame args, values state.1 ++ entry.limeSiteCode state.2⟩

open Wasm.Lime1.Execution in
def Entry.limeBefore {H : Type} (entry : Entry) (s : Store H) (outer : Frame) (index : FuncIdx)
    (args : List Value) (states : List OperandState) : List (Config H) :=
  limeSource s outer index args :: entry.limeInvoke s outer args ::
    (entry.cont.block.toList.map (fun _ => entry.limeBody s outer args) ++ states.map (entry.limeOperands s outer args))

open Wasm.Lime1.Execution in
def Entry.limePrefix {H : Type} (entry : Entry) (s : Store H) (outer : Frame) (index : FuncIdx)
    (args : List Value) (active : Source.Activation) (out : Outcome) (states : List OperandState) :
    List (Config H) :=
  entry.limeBefore s outer index args states ++
    [entry.cont.limeWrap outer (active.limeSource s entry.cont.scopes entry.cont.code),
     entry.cont.limeWrap outer (active.limeResolved s entry.cont.scopes entry.cont.code out)]

inductive LookupTrap : Outcome → Prop
  | bounds : LookupTrap .bounds
  | null : LookupTrap .null
  | mismatch (address : Runtime.FuncAddr) : LookupTrap (.mismatch address)

/-- A trap discards operands and pending instructions inside the active label.
With a block, it exits the block before the function label can discard its
own saved operands and tail. -/
inductive Cleanup (A : Type) where
  | block (scope : Blocks.Context.Scope A) (stack : List Value) (rest : List A)
  | label (stack : List Value) (rest : List A)
  | frame
  | done

inductive CleanupStep {A : Type} : Cleanup A → Cleanup A → Prop where
  | blockDiscard {scope : Blocks.Context.Scope A} {stack rest kept remaining}
      (cut : Prefix.Discard stack rest kept remaining) :
      CleanupStep (.block scope stack rest) (.block scope kept remaining)
  | blockExit (scope : Blocks.Context.Scope A) :
      CleanupStep (.block scope [] []) (.label scope.saved scope.rest)
  | discard {stack rest kept remaining} (cut : Prefix.Discard stack rest kept remaining) :
      CleanupStep (.label stack rest) (.label kept remaining)
  | label : CleanupStep (.label [] []) .frame
  | frame : CleanupStep .frame .done

abbrev CleanupRuns {A : Type} := Relation.ReflTransGen (@CleanupStep A)

def Entry.siteTrap {A : Type} (entry : Entry) (emit : Graph.Op → A)
    (stack : List Value) (rest : List A) : Cleanup A :=
  match entry.cont.block with
  | none => .label stack rest
  | some block => .block ⟨block.result.toList.length, entry.cont.owner.initial, block.tail.map emit⟩ stack rest

def Entry.coreTrapStart (entry : Entry) (active : Source.Activation) (out : Outcome) : Cleanup Core.Admin :=
  let pending := match out with
    | .bounds => [active.binding.site.coreCast, active.binding.site.coreCall]
    | .mismatch _ => [active.binding.site.coreCall]
    | _ => []
  entry.siteTrap Graph.coreEmit (active.operands.saved ++ active.operands.args) (pending ++ entry.cont.code.map Graph.coreEmit)

def Entry.limeTrapStart (entry : Entry) (active : Source.Activation) : Cleanup Wasm.Lime1.Execution.Admin :=
  entry.siteTrap Graph.limeEmit (active.operands.saved ++ active.operands.args) (entry.cont.code.map Graph.limeEmit)

def Entry.coreCleanup {H : Type} (entry : Entry) (s : Core.Store H) (outer inner : Frame) :
    Cleanup Core.Admin → Core.Config H
  | .block scope stack rest => entry.cont.coreWrap outer ⟨s, inner.toCore,
      scope.plug coreValues (fun n => .label n []) (coreValues stack ++ .trap :: rest)⟩
  | .label stack rest => entry.cont.coreWrap outer ⟨s, inner.toCore, coreValues stack ++ .trap :: rest⟩
  | .frame => ⟨s, outer.toCore, [.frame entry.cont.owner.declaration.results.length inner.toCore [.trap]]⟩
  | .done => ⟨s, outer.toCore, [.trap]⟩

open Wasm.Lime1.Execution in
def Entry.limeCleanup {H : Type} (entry : Entry) (s : Store H) (outer inner : Frame) :
    Cleanup Admin → Config H
  | .block scope stack rest => entry.cont.limeWrap outer ⟨s, inner,
      scope.plug values (fun n => .label n []) (values stack ++ .trap :: rest)⟩
  | .label stack rest => entry.cont.limeWrap outer ⟨s, inner, values stack ++ .trap :: rest⟩
  | .frame => ⟨s, outer, [.frame entry.cont.owner.declaration.results.length inner [.trap]]⟩
  | .done => ⟨s, outer, [.trap]⟩

def Entry.coreOperandResult {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame)
    (args : List Value) : OperandResult → Core.Config H
  | .values stack => entry.coreOperands s outer args (stack, [])
  | .trap saved rest => entry.coreCleanup s outer (entry.frame args) (entry.siteTrap Graph.coreEmit saved (entry.coreSiteCode rest))

open Wasm.Lime1.Execution in
def Entry.limeOperandResult {H : Type} (entry : Entry) (s : Store H) (outer : Frame)
    (args : List Value) : OperandResult → Config H
  | .values stack => entry.limeOperands s outer args (stack, [])
  | .trap saved rest => entry.limeCleanup s outer (entry.frame args) (entry.siteTrap Graph.limeEmit saved (entry.limeSiteCode rest))

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry
