module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Defs
public import Silmaril.Wasm.Institution.Operational.Locals.Native.Defs
public import Silmaril.Wasm.Institution.Operational.Blocks.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph

open Execution
open Execution.Runtime (Frame Value)
open Computed (ArgumentSyntax v1Syntax limeSyntax coreSyntax)
open Computed.Sequence (v1Source limeSource coreSource)

structure CodeSyntax (A : Type) where
  ops : ArgumentSyntax A
  set : LocalIdx → A
  tee : LocalIdx → A
  ret : A
  unreachable : A
  block : Option NumType → List A → A
  if_ : Option NumType → List A → List A → A
  br : LabelIdx → A
  brIf : LabelIdx → A

mutual

def Op.emit {A : Type} (codec : CodeSyntax A) : Op → A
  | .numeric op => Computed.Prefix.emit codec.ops op
  | .set i => codec.set i
  | .tee i => codec.tee i
  | .call target => codec.ops.call target.index
  | .block result code => codec.block result (Op.emitList codec code)
  | .if_ result thenBody elseBody =>
      codec.if_ result (Op.emitList codec thenBody) (Op.emitList codec elseBody)
  | .br depth _ => codec.br depth
  | .brIf depth _ => codec.brIf depth
  | .return_ => codec.ret
  | .unreachable => codec.unreachable

def Op.emitList {A : Type} (codec : CodeSyntax A) : List Op → List A
  | [] => []
  | op :: rest => op.emit codec :: Op.emitList codec rest

end

theorem Op.emitList_selected {A : Type} (codec : CodeSyntax A) (condition : BitVec 32)
    (thenBody elseBody : List Op) :
    Op.emitList codec (if condition = 0 then elseBody else thenBody) =
      (if condition = 0 then Op.emitList codec elseBody else Op.emitList codec thenBody) := by
  split <;> rfl

theorem Op.map_br_if {A : Type} (emit : Op → A) (condition : BitVec 32)
    (depth : LabelIdx) (result : Option NumType) (rest : List Op) :
    (if condition = 0 then rest else .br depth result :: rest).map emit =
      (if condition = 0 then [] else [emit (.br depth result)]) ++ rest.map emit := by
  split <;> rfl

def v1CodeSyntax : CodeSyntax Wasm.V1.Instr :=
  ⟨v1Source, .localSet, .localTee, .return_, .unreachable, .block, .if_, .br, .brIf⟩

def limeCodeSyntax : CodeSyntax Wasm.Lime1.Instr :=
  ⟨limeSource, .localSet, .localTee, .return_, .unreachable, .block ∘ Blocks.limeType, .if_ ∘ Blocks.limeType, .br, .brIf⟩

def coreCodeSyntax : CodeSyntax Instr :=
  ⟨coreSource, .localSet, .localTee, .return_, .unreachable, .block ∘ Blocks.coreType, .if_ ∘ Blocks.coreType, .br, .brIf⟩

def Function.instructions {A : Type} (fn : Function) (codec : CodeSyntax A) : List A :=
  fn.initial.map codec.ops.value ++ Op.emitList codec fn.code

def Function.v1Func (fn : Function) : Wasm.V1.Func :=
  ⟨fn.declaration.typeIndex, fn.declaration.locals, fn.instructions v1CodeSyntax⟩

def Function.limeFunc (fn : Function) : Wasm.Lime1.Func :=
  ⟨fn.declaration.typeIndex, fn.declaration.locals, fn.instructions limeCodeSyntax⟩

def Function.coreFunc (fn : Function) : Wasm.Func :=
  ⟨fn.declaration.typeIndex, fn.declaration.locals.map Wasm.V1.ValType.toCore, fn.instructions coreCodeSyntax⟩

def Function.coreInstance {H : Type} (fn : Function) : Core.FuncInst H :=
  ⟨fn.declaration.type.toDefType, fn.declaration.module.toCore, .wasm fn.coreFunc⟩

/-- Store allocation is checked against the exact source body for each occupied address. -/
def Program.CoreAllocated {H : Type} (program : Program) (s : Core.Store H) : Prop :=
  ∀ address fn, program.lookup address = some fn → s.funcs[address.value]? = some fn.coreInstance

def Program.LimeAllocated {H : Type} (program : Program) (s : Wasm.Lime1.Execution.Store H) : Prop :=
  ∀ address fn, program.lookup address = some fn →
    s.funcs[address.value]? = some (.wasm fn.declaration.type fn.declaration.module fn.limeFunc)

def Program.V1Allocated {H : Type} (program : Program) (s : Wasm.V1.Execution.Store H) : Prop :=
  ∀ address fn, program.lookup address = some fn →
    s.funcs[address.value]? = some (.wasm fn.declaration.type fn.declaration.module fn.v1Func)

structure Root (program : Program) (caller : Frame) (target : CallTarget) (fn : Function) : Prop where
  found : program.lookup target.address = some fn
  declared : fn.declaration = target.declaration
  resolves : target.Resolves caller

structure Syntax (A : Type) where
  ops : ArgumentSyntax A
  emit : Op → A
  values : List Value → List A
  ret : A
  trap : A
  invoke : CallTarget → List A
  frame : Nat → Frame → List A → A
  label : Nat → List A → A

mutual

def Phase.renderAt {A : Type} (ops : Syntax A) (target : CallTarget) (n : Nat) : Phase → List A
  | .call args => ops.values args ++ [ops.ops.call target.index]
  | .invoke args => ops.values args ++ ops.invoke target
  | .label locals body =>
      [ops.frame n (currentFrame target.declaration locals) [ops.label n (body.render ops)]]
  | .branching locals stack depth result =>
      [ops.frame n (currentFrame target.declaration locals) (ops.values stack ++ [ops.emit (.br depth result)])]
  | .returning locals stack =>
      [ops.frame n (currentFrame target.declaration locals)
        (ops.values stack ++ [ops.ret])]
  | .exit locals result =>
      [ops.frame n (currentFrame target.declaration locals)
        (Nested.resultCode ops.values ops.trap result)]
  | .done result => Nested.resultCode ops.values ops.trap result

def Body.render {A : Type} (ops : Syntax A) : Body → List A
  | .running stack rest => ops.values stack ++ rest.map ops.emit
  | .active saved target child rest =>
      ops.values saved ++ child.renderAt ops target target.declaration.results.length ++ rest.map ops.emit
  | .block saved result body rest =>
      ops.values saved ++ ops.label result.toList.length (body.render ops) :: rest.map ops.emit
  | .trapped saved rest => ops.values saved ++ ops.trap :: rest.map ops.emit

end

def Phase.render {A : Type} (ops : Syntax A) (target : CallTarget) : Phase → List A :=
  Phase.renderAt ops target target.declaration.results.length

def v1Emit : Op → Wasm.V1.Execution.Admin
  | .numeric op => Computed.Prefix.emit v1Syntax op
  | op => .source (op.emit v1CodeSyntax)

def v1Admin : Syntax Wasm.V1.Execution.Admin :=
  ⟨v1Syntax, v1Emit, Wasm.V1.Execution.values,
    .source .return_, .trap, fun t => [.invoke t.address], .frame, fun n => .label n []⟩

def limeEmit : Op → Wasm.Lime1.Execution.Admin
  | .numeric op => Computed.Prefix.emit limeSyntax op
  | op => .source (op.emit limeCodeSyntax)

def limeAdmin : Syntax Wasm.Lime1.Execution.Admin :=
  ⟨limeSyntax, limeEmit, Wasm.Lime1.Execution.values,
    .source .return_, .trap, fun t => [.invoke t.address], .frame, fun n => .label n []⟩

def coreEmit : Op → Core.Admin
  | .numeric op => Computed.Prefix.emit coreSyntax op
  | op => .plain (op.emit coreCodeSyntax)

def coreAdmin : Syntax Core.Admin :=
  ⟨coreSyntax, coreEmit, coreValues, .plain .return_, .trap,
    fun t => [.ref (.func t.address.value), .callRefType t.declaration.type.toDefType],
    fun n f => .frame n f.toCore, fun n => .label n []⟩

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (target : CallTarget) (q : Phase) :
    Wasm.V1.Execution.Config H := ⟨s, caller, q.render v1Admin target⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (target : CallTarget) (q : Phase) :
    Wasm.Lime1.Execution.Config H := ⟨s, caller, q.render limeAdmin target⟩

def coreConfig {H : Type} (s : Core.Store H) (caller : Frame) (target : CallTarget) (q : Phase) :
    Core.Config H := ⟨s, caller.toCore, q.render coreAdmin target⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph
