module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry

open Execution
open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Context.Resume (Continuation)

/-- At this designated graph address the allocated Wasm body begins with the
literal operand prefix and the indirect site. Its declaration and continuation
targets are taken from the registered graph function. -/
structure Entry where
  cont : Continuation
  op : Source.Op

def Entry.body (entry : Entry) : Source.Body := .indirect [] entry.op entry.cont.code

def Entry.check (entry : Entry) (program : Graph.Program) (tables : Source.Tables) : Bool :=
  let fn := entry.cont.owner
  program.checkDirect && entry.body.checkRegion program tables fn fn.declaration.results [] (Prefix.stackTypes fn.initial)

def Entry.prepare (entry : Entry) (program : Graph.Program) (tables : Source.Tables) (args : List Value) :
    Option Source.Activation :=
  if args.map Value.type = entry.cont.owner.declaration.params then
    entry.op.prepare program tables (entry.cont.owner.declaration.frame args) entry.cont.owner.initial
  else none

structure Entry.Checked (entry : Entry) (program : Graph.Program) (tables : Source.Tables)
    (outer : Frame) (index : FuncIdx) (args : List Value) (active : Source.Activation) : Prop where
  source : entry.check program tables = true
  found : program.lookup entry.cont.address = some entry.cont.owner
  resolves : outer.module.funcs[index.toNat]? = some entry.cont.address
  typed : args.map Value.type = entry.cont.owner.declaration.params
  prepared : entry.prepare program tables args = some active

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

def Entry.coreLookup {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame)
    (active : Source.Activation) (phase : Indirect.Phase) : Core.Config H :=
  entry.cont.coreWrap outer (active.coreConfig s [] entry.cont.code phase)

def Entry.corePrefix {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame) (index : FuncIdx)
    (args : List Value) (active : Source.Activation) (out : Outcome) : List (Core.Config H) :=
  [coreSource s outer index args, entry.coreInvoke s outer args] ++
    out.coreTrace.map (entry.coreLookup s outer active)

open Wasm.Lime1.Execution in
def limeSource {H : Type} (s : Store H) (outer : Frame) (index : FuncIdx) (args : List Value) : Config H :=
  ⟨s, outer, values args ++ [.source (.call index)]⟩

open Wasm.Lime1.Execution in
def Entry.limeInvoke {H : Type} (entry : Entry) (s : Store H) (outer : Frame) (args : List Value) : Config H :=
  ⟨s, outer, values args ++ [.invoke entry.cont.address]⟩

open Wasm.Lime1.Execution in
def Entry.limePrefix {H : Type} (entry : Entry) (s : Store H) (outer : Frame) (index : FuncIdx)
    (args : List Value) (active : Source.Activation) (out : Outcome) : List (Config H) :=
  [limeSource s outer index args, entry.limeInvoke s outer args,
    entry.cont.limeWrap outer (active.limeSource s [] entry.cont.code),
    entry.cont.limeWrap outer (active.limeResolved s [] entry.cont.code out)]

inductive LookupTrap : Outcome → Prop
  | bounds : LookupTrap .bounds
  | null : LookupTrap .null
  | mismatch (address : Runtime.FuncAddr) : LookupTrap (.mismatch address)

/-- A trap first discards portions of the label's operand and instruction
context, then leaves the label and function frame. -/
inductive Cleanup (A : Type) where
  | label (stack : List Value) (rest : List A)
  | frame
  | done

inductive CleanupStep {A : Type} : Cleanup A → Cleanup A → Prop where
  | discard {stack rest kept remaining} (cut : Prefix.Discard stack rest kept remaining) :
      CleanupStep (.label stack rest) (.label kept remaining)
  | label : CleanupStep (.label [] []) .frame
  | frame : CleanupStep .frame .done

abbrev CleanupRuns {A : Type} := Relation.ReflTransGen (@CleanupStep A)

def Entry.coreTrapStart (entry : Entry) (active : Source.Activation) (out : Outcome) : Cleanup Core.Admin :=
  let pending := match out with
    | .bounds => [active.binding.site.coreCast, active.binding.site.coreCall]
    | .mismatch _ => [active.binding.site.coreCall]
    | _ => []
  .label (active.operands.saved ++ active.operands.args) (pending ++ entry.cont.code.map Graph.coreEmit)

def Entry.limeTrapStart (entry : Entry) (active : Source.Activation) : Cleanup Wasm.Lime1.Execution.Admin :=
  .label (active.operands.saved ++ active.operands.args) (entry.cont.code.map Graph.limeEmit)

def Entry.coreCleanup {H : Type} (entry : Entry) (s : Core.Store H) (outer inner : Frame) :
    Cleanup Core.Admin → Core.Config H
  | .label stack rest => entry.cont.coreWrap outer ⟨s, inner.toCore, coreValues stack ++ .trap :: rest⟩
  | .frame => ⟨s, outer.toCore, [.frame entry.cont.owner.declaration.results.length inner.toCore [.trap]]⟩
  | .done => ⟨s, outer.toCore, [.trap]⟩

open Wasm.Lime1.Execution in
def Entry.limeCleanup {H : Type} (entry : Entry) (s : Store H) (outer inner : Frame) :
    Cleanup Admin → Config H
  | .label stack rest => entry.cont.limeWrap outer ⟨s, inner, values stack ++ .trap :: rest⟩
  | .frame => ⟨s, outer, [.frame entry.cont.owner.declaration.results.length inner [.trap]]⟩
  | .done => ⟨s, outer, [.trap]⟩

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry
