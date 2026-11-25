module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source

open Execution
open Execution.Runtime (Frame FuncAddr ModuleInst TableAddr TableInst Value)
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

/-- A numeric indirect source operator at table index zero. The signature
annotation is checked against the current module's type index. -/
structure Op where
  typeIndex : TypeIdx
  signature : V1.FuncType
  deriving DecidableEq

def Op.coreInstr (op : Op) : Instr := .callIndirect tableIndex op.typeIndex

def Op.limeInstr (op : Op) : Wasm.Lime1.Instr := .callIndirect op.typeIndex

/-- Stack types are top-first. The selector sits above the complete argument
suffix. Results replace that suffix in their declared order. -/
def Op.checkStack (op : Op) (types : List V1.FuncType) : List NumType → Option (List NumType)
  | .int .i32 :: operands =>
      if types[op.typeIndex.toNat]? = some op.signature ∧
        operands.take op.signature.params.length = op.signature.params.reverse then
        some (op.signature.results.reverse ++ operands.drop op.signature.params.length)
      else none
  | _ => none

/-- An address-indexed snapshot of the fixed read-only tables used by the fragment. -/
abbrev Tables := List TableInst

def Tables.CoreAllocated {H : Type} (tables : Tables) (s : Core.Store H) : Prop :=
  ∀ addr : TableAddr, ∀ table, tables[addr.value]? = some table → s.tables[addr.value]? = some table.toCore

def Tables.LimeAllocated {H : Type} (tables : Tables) (s : Wasm.Lime1.Execution.Store H) : Prop :=
  ∀ addr : TableAddr, ∀ table, tables[addr.value]? = some table → s.tables[addr.value]? = some table

structure Binding where
  address : TableAddr
  site : Site

/-- Resolve the table from the activation's module and check the type index
and every nonnull declaration. Valid entries with a different signature are
allowed, so the native mismatch trap remains observable. -/
def Op.bind (op : Op) (program : Graph.Program) (tables : Tables) (caller : ModuleInst) : Option Binding := do
  let address ← caller.tables[tableIndex.toNat]?
  let table ← tables[address.value]?
  let site : Site := ⟨table, op.typeIndex, op.signature⟩
  if site.check program ⟨[], caller⟩ then some ⟨address, site⟩ else none

structure Operands where
  saved : List Value
  args : List Value
  selector : BitVec 32

def Op.split (op : Op) (stack : List Value) : Option Operands :=
  match stack.reverse with
  | ⟨.int .i32, selector⟩ :: operands =>
      let args := (operands.take op.signature.params.length).reverse
      if args.map Value.type = op.signature.params then
        some ⟨(operands.drop op.signature.params.length).reverse, args, selector⟩
      else none
  | _ => none

structure Activation where
  caller : Frame
  binding : Binding
  operands : Operands

def Op.prepare (op : Op) (program : Graph.Program) (tables : Tables) (caller : Frame)
    (stack : List Value) : Option Activation := do
  let binding ← op.bind program tables caller.module
  let operands ← op.split stack
  return ⟨caller, binding, operands⟩

def Activation.resolve (active : Activation) (program : Graph.Program) : Option Outcome :=
  active.binding.site.resolve program active.operands.selector

/-- Only successful resolution supplies a graph invocation. Lookup traps
remain distinct outcomes of `resolve`. -/
def Activation.invocation (active : Activation) (program : Graph.Program) : Option Context.Invocation := do
  let .resolved address ← active.resolve program | none
  let callee ← program.lookup address
  return ⟨active.binding.site, active.caller, active.operands.selector, active.operands.saved,
    active.operands.args, address, callee⟩

structure Activation.Checked (active : Activation) (program : Graph.Program) (tables : Tables) : Prop where
  addressed : active.caller.module.tables[tableIndex.toNat]? = some active.binding.address
  table : tables[active.binding.address.value]? = some active.binding.site.table
  site : active.binding.site.check program active.caller = true
  args : active.operands.args.map Value.type = active.binding.site.signature.params

structure Op.Prepared (op : Op) (program : Graph.Program) (tables : Tables)
    (caller : Frame) (stack : List Value) (active : Activation) : Prop where
  caller_eq : active.caller = caller
  checked : active.Checked program tables
  typeIndex_eq : active.binding.site.typeIndex = op.typeIndex
  signature_eq : active.binding.site.signature = op.signature
  stack_eq : stack = active.operands.saved ++ active.operands.args ++ [Value.int .i32 active.operands.selector]

def Op.checkTail (op : Op) (fn : Graph.Function) (fallthrough : List NumType)
    (enclosing : Graph.EnclosingLabels) (stack : List NumType) (tail : List Graph.Op) : Bool :=
  ((op.checkStack fn.declaration.module.types stack).map fun next =>
    Graph.checkCode fn.targets fn.localTypes fn.declaration.results fallthrough enclosing next tail
      .exit fn.declaration.module.types).getD false

/-- A source region with one designated indirect site at the end of a numeric
prefix. Parameterless scalar blocks may surround the site. Every pending
tail uses the existing graph syntax and checker. -/
inductive Body where
  | indirect (before : List Prefix.Op) (op : Op) (tail : List Graph.Op)
  | block (result : Option NumType) (inside : Body) (tail : List Graph.Op)

def Body.checkRegion (program : Graph.Program) (tables : Tables) (fn : Graph.Function)
    (fallthrough : List NumType) (enclosing : Graph.EnclosingLabels) (stack : List NumType) : Body → Bool
  | .indirect before op tail =>
      (op.bind program tables fn.declaration.module).isSome &&
        ((Prefix.check fn.localTypes stack before).map fun atCall =>
          op.checkTail fn fallthrough enclosing atCall tail).getD false
  | .block result inside tail =>
      inside.checkRegion program tables fn result.toList (fallthrough :: enclosing) [] &&
        Graph.checkCode fn.targets fn.localTypes fn.declaration.results fallthrough enclosing
          (result.toList.reverse ++ stack) tail .exit fn.declaration.module.types

def Body.check (body : Body) (program : Graph.Program) (tables : Tables) (address : FuncAddr) : Bool :=
  program.checkDirect && ((program.lookup address).map fun fn =>
    body.checkRegion program tables fn fn.declaration.results [] (Prefix.stackTypes fn.initial)).getD false

def Body.emit {I : Type} (codec : Graph.CodeSyntax I) (call : Op → I) : Body → List I
  | .indirect before op tail =>
      before.map (fun p => Graph.Op.emit codec (.numeric p)) ++ call op :: Graph.Op.emitList codec tail
  | .block result inside tail =>
      codec.block result (inside.emit codec call) :: Graph.Op.emitList codec tail

def Body.core (body : Body) : List Instr := body.emit Graph.coreCodeSyntax Op.coreInstr

def Body.lime (body : Body) : List Wasm.Lime1.Instr := body.emit Graph.limeCodeSyntax Op.limeInstr

/-- The single site and its immediate continuation, under any surrounding
scalar blocks in this source region. -/
def Body.operation : Body → Op
  | .indirect _ op _ => op
  | .block _ inside _ => inside.operation

def Body.siteTail : Body → List Graph.Op
  | .indirect _ _ tail => tail
  | .block _ inside _ => inside.siteTail

def Body.scopes (saved : List Value) : Body → List (Blocks.Context.Scope Graph.Op)
  | .indirect .. => []
  | .block result inside tail => ⟨result.toList.length, saved, tail⟩ :: inside.scopes []

abbrev coreNest := @Context.coreNest

abbrev limeNest := @Context.limeNest

def Activation.coreConfig {H : Type} (active : Activation) (s : Core.Store H)
    (scopes : List (Blocks.Context.Scope Graph.Op)) (tail : List Graph.Op) (phase : Indirect.Phase) : Core.Config H :=
  coreNest scopes (Indirect.coreConfig s active.caller active.binding.site active.operands.selector
    (active.operands.saved ++ active.operands.args) (tail.map Graph.coreEmit) phase)

def Activation.limeSource {H : Type} (active : Activation) (s : Wasm.Lime1.Execution.Store H)
    (scopes : List (Blocks.Context.Scope Graph.Op)) (tail : List Graph.Op) : Wasm.Lime1.Execution.Config H :=
  limeNest scopes (Indirect.limeSource s active.caller active.binding.site active.operands.selector
    (active.operands.saved ++ active.operands.args) (tail.map Graph.limeEmit))

def Activation.limeResolved {H : Type} (active : Activation) (s : Wasm.Lime1.Execution.Store H)
    (scopes : List (Blocks.Context.Scope Graph.Op)) (tail : List Graph.Op) (out : Outcome) :
    Wasm.Lime1.Execution.Config H :=
  limeNest scopes (Indirect.limeResolved s active.caller (active.operands.saved ++ active.operands.args)
    (tail.map Graph.limeEmit) out)

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source
