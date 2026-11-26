module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional

open Execution
open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

/-- An entry conditional with a local i32 condition at the function label.
One arm contains the designated site, under any checked block spine.
The other arm and the enclosing continuation use ordinary graph code. -/
structure Entry where
  inside : GraphEntry.Entry
  condition : LocalIdx
  result : Option NumType
  alternate : List Graph.Op
  tail : List Graph.Op
  siteOnTrue : Bool := true

def Entry.site (entry : Entry) : GraphEntry.Entry :=
  { entry.inside with cont := { entry.inside.cont with
    blocks := ⟨entry.result, entry.tail⟩ :: entry.inside.cont.blocks } }

def Entry.alternateCode (entry : Entry) : List Graph.Op :=
  .block entry.result entry.alternate :: entry.tail

def Entry.alternatePhase (entry : Entry) (args : List Value) : Graph.Phase :=
  .label (entry.site.frame args).locals (.running entry.site.cont.owner.initial entry.alternateCode)

def Entry.check (entry : Entry) (program : Graph.Program) (tables : Source.Tables) : Bool :=
  let fn := entry.site.cont.owner
  entry.site.check program tables &&
    decide (fn.localTypes[entry.condition.toNat]? = some (.int .i32)) &&
    Graph.checkCode fn.targets fn.localTypes fn.declaration.results fn.declaration.results []
      (Prefix.stackTypes fn.initial) entry.alternateCode .exit fn.declaration.module.types

structure Entry.Checked (entry : Entry) (program : Graph.Program) (tables : Source.Tables)
    (outer : Frame) (index : FuncIdx) (args : List Value) : Prop where
  source : entry.check program tables = true
  found : program.lookup entry.site.cont.address = some entry.site.cont.owner
  resolves : outer.module.funcs[index.toNat]? = some entry.site.cont.address
  typed : args.map Value.type = entry.site.cont.owner.declaration.params

def Entry.Condition (entry : Entry) (args : List Value) (value : BitVec 32) : Prop :=
  (entry.site.frame args).locals[entry.condition.toNat]? = some (.int .i32 value)

def Entry.choosesSite (entry : Entry) (value : BitVec 32) : Bool :=
  if value = 0 then !entry.siteOnTrue else entry.siteOnTrue

def Entry.arms {A : Type} (entry : Entry) (site alternate : A) : A × A :=
  if entry.siteOnTrue then (site, alternate) else (alternate, site)

def Entry.coreIf (entry : Entry) : Instr :=
  let arms := entry.arms entry.inside.body.core (Graph.Op.emitList Graph.coreCodeSyntax entry.alternate)
  .if_ (Blocks.coreType entry.result) arms.1 arms.2

def Entry.limeIf (entry : Entry) : Wasm.Lime1.Instr :=
  let arms := entry.arms entry.inside.body.lime (Graph.Op.emitList Graph.limeCodeSyntax entry.alternate)
  .if_ (Blocks.limeType entry.result) arms.1 arms.2

def Entry.coreFunc (entry : Entry) : Wasm.Func :=
  let code := entry.site.cont.owner.initial.map Graph.coreCodeSyntax.ops.value ++
    (Instr.localGet entry.condition :: entry.coreIf :: Graph.Op.emitList Graph.coreCodeSyntax entry.tail)
  { entry.site.coreFunc with body := code }

def Entry.limeFunc (entry : Entry) : Wasm.Lime1.Func :=
  let code := entry.site.cont.owner.initial.map Graph.limeCodeSyntax.ops.value ++
    (Wasm.Lime1.Instr.localGet entry.condition :: entry.limeIf :: Graph.Op.emitList Graph.limeCodeSyntax entry.tail)
  { entry.site.limeFunc with body := code }

def Entry.coreInstance {H : Type} (entry : Entry) : Core.FuncInst H :=
  let decl := entry.site.cont.owner.declaration
  ⟨decl.type.toDefType, decl.module.toCore, .wasm entry.coreFunc⟩

def Entry.limeInstance {H : Type} (entry : Entry) : Runtime.FuncInst Wasm.Lime1.Func H :=
  let decl := entry.site.cont.owner.declaration
  .wasm decl.type decl.module entry.limeFunc

def Entry.coreRead {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame) (args : List Value) :
    Core.Config H :=
  entry.site.cont.coreWrap outer ⟨s, (entry.site.frame args).toCore, Core.expression entry.coreFunc.body⟩

open Wasm.Lime1.Execution in
def Entry.limeRead {H : Type} (entry : Entry) (s : Store H) (outer : Frame) (args : List Value) : Config H :=
  entry.site.cont.limeWrap outer ⟨s, entry.site.frame args, expression entry.limeFunc.body⟩

def Entry.coreTest {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame) (args : List Value)
    (value : BitVec 32) : Core.Config H :=
  entry.site.cont.coreWrap outer ⟨s, (entry.site.frame args).toCore,
    coreValues (entry.site.cont.owner.initial ++ [.int .i32 value]) ++
      .plain entry.coreIf :: entry.tail.map Graph.coreEmit⟩

open Wasm.Lime1.Execution in
def Entry.limeTest {H : Type} (entry : Entry) (s : Store H) (outer : Frame) (args : List Value)
    (value : BitVec 32) : Config H :=
  entry.site.cont.limeWrap outer ⟨s, entry.site.frame args,
    values (entry.site.cont.owner.initial ++ [.int .i32 value]) ++
      .source entry.limeIf :: entry.tail.map Graph.limeEmit⟩

def Entry.coreFront {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame) (args : List Value)
    (value : BitVec 32) : List (Core.Config H) :=
  [entry.site.coreInvoke s outer args, entry.coreRead s outer args, entry.coreTest s outer args value]

open Wasm.Lime1.Execution in
def Entry.limeFront {H : Type} (entry : Entry) (s : Store H) (outer : Frame) (args : List Value)
    (value : BitVec 32) : List (Config H) :=
  [entry.site.limeInvoke s outer args, entry.limeRead s outer args, entry.limeTest s outer args value]

def Entry.coreSelected {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame) (args : List Value)
    (value : BitVec 32) : Core.Config H :=
  if entry.choosesSite value then entry.site.coreBody s outer args
  else Graph.coreConfig s outer entry.site.cont.target (entry.alternatePhase args)

open Wasm.Lime1.Execution in
def Entry.limeSelected {H : Type} (entry : Entry) (s : Store H) (outer : Frame) (args : List Value)
    (value : BitVec 32) : Config H :=
  if entry.choosesSite value then entry.site.limeBody s outer args
  else Graph.limeConfig s outer entry.site.cont.target (entry.alternatePhase args)

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Conditional
