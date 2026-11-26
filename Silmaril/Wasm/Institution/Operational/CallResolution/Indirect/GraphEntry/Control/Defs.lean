module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control

open Execution
open Execution.Runtime (Frame FuncAddr Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Context.Resume (Block)

structure Choice where
  condition : LocalIdx
  alternate : List Graph.Op
  siteOnTrue : Bool := true

def Choice.takesSite (choice : Choice) (value : BitVec 32) : Bool :=
  if value = 0 then !choice.siteOnTrue else choice.siteOnTrue

def Choice.arms {A : Type} (choice : Choice) (path alternate : A) : A × A :=
  if choice.siteOnTrue then (path, alternate) else (alternate, path)

/-- Both control instructions enter the same scalar block context when
execution continues toward the site. -/
structure Node where
  block : Block
  choice : Option Choice := none

def Node.alternateCode (block : Block) (choice : Choice) : List Graph.Op :=
  .block block.result choice.alternate :: block.tail

def Node.switch {I : Type} (codec : Graph.CodeSyntax I) (block : Block) (choice : Choice) (inside : List I) : I :=
  let arms := choice.arms inside (Graph.Op.emitList codec choice.alternate)
  codec.if_ block.result arms.1 arms.2

def Node.emit {I : Type} (codec : Graph.CodeSyntax I) (node : Node) (inside : List I) : List I :=
  let tail := Graph.Op.emitList codec node.block.tail
  match node.choice with
  | none => codec.block node.block.result inside :: tail
  | some choice => codec.ops.get choice.condition :: Node.switch codec node.block choice inside :: tail

/-- The path is in source order. Each conditional has a single successor
toward the site and an alternate arm in the existing direct graph syntax. -/
structure Entry where
  address : FuncAddr
  owner : Graph.Function
  tail : List Graph.Op
  op : Source.Op
  before : List Prefix.Op
  nodes : List Node

def Entry.cont (entry : Entry) : Context.Resume.Continuation :=
  ⟨entry.address, entry.owner, entry.tail, entry.nodes.map Node.block⟩

def Entry.site (entry : Entry) : GraphEntry.Entry :=
  ⟨entry.cont, entry.op, entry.before⟩

def Entry.saved (entry : Entry) (entered : List Block) : List Value :=
  if entered.isEmpty then entry.cont.owner.initial else []

def Entry.withBlocks (entry : Entry) (entered : List Block) : Context.Resume.Continuation :=
  { entry.cont with blocks := entered }

def Entry.choiceCheck (entry : Entry) (entered : List Block) (block : Block) (choice : Choice) : Bool :=
  let fn := entry.cont.owner
  let context := Block.context entered fn.declaration.results []
  decide (fn.localTypes[choice.condition.toNat]? = some (.int .i32)) &&
    Block.check fn entered fn.initial fn.declaration.results [] &&
    Graph.checkCode fn.targets fn.localTypes fn.declaration.results context.1 context.2
      (Prefix.stackTypes (entry.saved entered)) (Node.alternateCode block choice) .exit fn.declaration.module.types

def Entry.checkNodes (entry : Entry) (entered : List Block) : List Node → Bool
  | [] => true
  | node :: rest => node.choice.all (entry.choiceCheck entered node.block) &&
      entry.checkNodes (entered ++ [node.block]) rest

def Entry.check (entry : Entry) (program : Graph.Program) (tables : Source.Tables) : Bool :=
  entry.site.check program tables && entry.checkNodes [] entry.nodes

structure Entry.Checked (entry : Entry) (program : Graph.Program) (tables : Source.Tables)
    (outer : Frame) (index : FuncIdx) (args : List Value) : Prop where
  source : entry.check program tables = true
  found : program.lookup entry.cont.address = some entry.cont.owner
  resolves : outer.module.funcs[index.toNat]? = some entry.cont.address
  typed : args.map Value.type = entry.cont.owner.declaration.params

def Entry.emit {I : Type} (entry : Entry) (codec : Graph.CodeSyntax I) (call : Source.Op → I)
    (nodes : List Node) : List I :=
  nodes.foldr (Node.emit codec) (entry.site.siteBody.emit codec call)

inductive Position where
  | pending (entered : List Block) (rest : List Node)
  | test (entered : List Block) (block : Block) (choice : Choice) (rest : List Node) (value : BitVec 32)

inductive Endpoint where
  | site (entered : List Block)
  | alternate (entered : List Block) (code : List Graph.Op)

/-- A trace stops at the first alternate arm or at the operand prefix.
The trace includes the native lowering of an if before block entry. -/
inductive Trace (locals : List Value) :
    List Block → List Node → List Position → Endpoint → Prop where
  | done (entered) : Trace locals entered [] [] (.site entered)
  | block {entered block rest states endpoint}
      (next : Trace locals (entered ++ [block]) rest states endpoint) :
      Trace locals entered (⟨block, none⟩ :: rest) (.pending entered (⟨block, none⟩ :: rest) :: states) endpoint
  | taken {entered block choice rest value states endpoint}
      (read : locals[choice.condition.toNat]? = some (.int .i32 value)) (select : choice.takesSite value = true)
      (next : Trace locals entered (⟨block, none⟩ :: rest) states endpoint) :
      Trace locals entered (⟨block, some choice⟩ :: rest)
        (.pending entered (⟨block, some choice⟩ :: rest) :: .test entered block choice rest value :: states) endpoint
  | alternate {entered block choice rest value}
      (read : locals[choice.condition.toNat]? = some (.int .i32 value)) (select : choice.takesSite value = false) :
      Trace locals entered (⟨block, some choice⟩ :: rest)
        [.pending entered (⟨block, some choice⟩ :: rest), .test entered block choice rest value]
        (.alternate entered (Node.alternateCode block choice))

abbrev Entry.Trace (entry : Entry) (args : List Value) :=
  Control.Trace (entry.site.frame args).locals [] entry.nodes

def Entry.alternatePhase (entry : Entry) (args : List Value) (entered : List Block)
    (code : List Graph.Op) : Graph.Phase :=
  .label (entry.site.frame args).locals ((entry.withBlocks entered).plug (.running (entry.saved entered) code))

def Entry.coreFunc (entry : Entry) : Wasm.Func :=
  let code := entry.cont.owner.initial.map Graph.coreCodeSyntax.ops.value ++
    entry.emit Graph.coreCodeSyntax Source.Op.coreInstr entry.nodes
  { entry.site.coreFunc with body := code }

def Entry.limeFunc (entry : Entry) : Wasm.Lime1.Func :=
  let code := entry.cont.owner.initial.map Graph.limeCodeSyntax.ops.value ++
    entry.emit Graph.limeCodeSyntax Source.Op.limeInstr entry.nodes
  { entry.site.limeFunc with body := code }

def Entry.coreInstance {H : Type} (entry : Entry) : Core.FuncInst H :=
  let decl := entry.cont.owner.declaration
  ⟨decl.type.toDefType, decl.module.toCore, .wasm entry.coreFunc⟩

def Entry.limeInstance {H : Type} (entry : Entry) : Runtime.FuncInst Wasm.Lime1.Func H :=
  let decl := entry.cont.owner.declaration
  .wasm decl.type decl.module entry.limeFunc

def Entry.corePosition {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame) (args : List Value) :
    Position → Core.Config H
  | .pending entered rest => (entry.withBlocks entered).coreSiteWrap outer ⟨s, (entry.site.frame args).toCore,
      coreValues (entry.saved entered) ++ Core.expression (entry.emit Graph.coreCodeSyntax Source.Op.coreInstr rest)⟩
  | .test entered block choice rest value =>
      (entry.withBlocks entered).coreSiteWrap outer ⟨s, (entry.site.frame args).toCore,
        coreValues (entry.saved entered ++ [.int .i32 value]) ++
          .plain (Node.switch Graph.coreCodeSyntax block choice (entry.emit Graph.coreCodeSyntax Source.Op.coreInstr rest)) ::
            block.tail.map Graph.coreEmit⟩

open Wasm.Lime1.Execution in
def Entry.limePosition {H : Type} (entry : Entry) (s : Store H) (outer : Frame) (args : List Value) :
    Position → Config H
  | .pending entered rest => (entry.withBlocks entered).limeSiteWrap outer ⟨s, entry.site.frame args,
      values (entry.saved entered) ++ expression (entry.emit Graph.limeCodeSyntax Source.Op.limeInstr rest)⟩
  | .test entered block choice rest value =>
      (entry.withBlocks entered).limeSiteWrap outer ⟨s, entry.site.frame args,
        values (entry.saved entered ++ [.int .i32 value]) ++
          .source (Node.switch Graph.limeCodeSyntax block choice (entry.emit Graph.limeCodeSyntax Source.Op.limeInstr rest)) ::
            block.tail.map Graph.limeEmit⟩

def Entry.coreEnd {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame) (args : List Value) :
    Endpoint → Core.Config H
  | .site entered => entry.corePosition s outer args (.pending entered [])
  | .alternate entered code => Graph.coreConfig s outer entry.cont.target (entry.alternatePhase args entered code)

open Wasm.Lime1.Execution in
def Entry.limeEnd {H : Type} (entry : Entry) (s : Store H) (outer : Frame) (args : List Value) :
    Endpoint → Config H
  | .site entered => entry.limePosition s outer args (.pending entered [])
  | .alternate entered code => Graph.limeConfig s outer entry.cont.target (entry.alternatePhase args entered code)

def Entry.coreFront {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame) (args : List Value)
    (states : List Position) : List (Core.Config H) :=
  entry.site.coreInvoke s outer args :: states.map (entry.corePosition s outer args)

open Wasm.Lime1.Execution in
def Entry.limeFront {H : Type} (entry : Entry) (s : Store H) (outer : Frame) (args : List Value)
    (states : List Position) : List (Config H) :=
  entry.site.limeInvoke s outer args :: states.map (entry.limePosition s outer args)

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Control
