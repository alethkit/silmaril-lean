module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Defs
public import Silmaril.Wasm.Institution.Operational.Locals.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph

open Execution
open Execution.Runtime (Frame Value)
open Computed (ArgumentSyntax v1Syntax limeSyntax coreSyntax)
open Computed.Sequence (v1Source limeSource coreSource)

def Op.emit {A : Type} (ops : ArgumentSyntax A) (set tee : LocalIdx → A) (ret unreachable : A) : Op → A
  | .numeric op => Computed.Prefix.emit ops op
  | .set i => set i
  | .tee i => tee i
  | .call target => ops.call target.index
  | .return_ => ret
  | .unreachable => unreachable

def Function.instructions {A : Type} (fn : Function) (ops : ArgumentSyntax A) (set tee : LocalIdx → A) (ret unreachable : A) : List A :=
  fn.initial.map ops.value ++ fn.code.map (Op.emit ops set tee ret unreachable)

def Function.v1Func (fn : Function) : Wasm.V1.Func :=
  ⟨fn.declaration.typeIndex, fn.declaration.locals,
    fn.instructions v1Source (Locals.v1Instr ∘ .set) (Locals.v1Instr ∘ .tee) .return_ .unreachable⟩

def Function.limeFunc (fn : Function) : Wasm.Lime1.Func :=
  ⟨fn.declaration.typeIndex, fn.declaration.locals,
    fn.instructions limeSource (Locals.limeInstr ∘ .set) (Locals.limeInstr ∘ .tee) .return_ .unreachable⟩

def Function.coreFunc (fn : Function) : Wasm.Func :=
  ⟨fn.declaration.typeIndex, fn.declaration.locals.map Wasm.V1.ValType.toCore,
    fn.instructions coreSource (Locals.coreInstr ∘ .set) (Locals.coreInstr ∘ .tee) .return_ .unreachable⟩

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
  set : LocalIdx → A
  tee : LocalIdx → A
  values : List Value → List A
  ret : A
  unreachable : A
  trap : A
  invoke : CallTarget → List A
  frame : Nat → Frame → List A → A
  label : Nat → List A → A

def Syntax.emit {A : Type} (ops : Syntax A) : Op → A :=
  Op.emit ops.ops ops.set ops.tee ops.ret ops.unreachable

mutual

def Phase.render {A : Type} (ops : Syntax A) (target : CallTarget) : Phase → List A
  | .call args => ops.values args ++ [ops.ops.call target.index]
  | .invoke args => ops.values args ++ ops.invoke target
  | .label locals body =>
      let n := target.declaration.results.length
      [ops.frame n (currentFrame target.declaration locals) [ops.label n (body.render ops)]]
  | .returning locals stack =>
      [ops.frame target.declaration.results.length (currentFrame target.declaration locals)
        (ops.values stack ++ [ops.ret])]
  | .exit locals result =>
      [ops.frame target.declaration.results.length (currentFrame target.declaration locals)
        (Nested.resultCode ops.values ops.trap result)]
  | .done result => Nested.resultCode ops.values ops.trap result

def Body.render {A : Type} (ops : Syntax A) : Body → List A
  | .running stack rest => ops.values stack ++ rest.map ops.emit
  | .active saved target child rest =>
      ops.values saved ++ child.render ops target ++ rest.map ops.emit
  | .trapped saved rest => ops.values saved ++ ops.trap :: rest.map ops.emit

end

def v1Admin : Syntax Wasm.V1.Execution.Admin :=
  ⟨v1Syntax, .source ∘ .localSet, .source ∘ .localTee, Wasm.V1.Execution.values,
    .source .return_, .source .unreachable, .trap, fun t => [.invoke t.address], .frame, fun n => .label n []⟩

def limeAdmin : Syntax Wasm.Lime1.Execution.Admin :=
  ⟨limeSyntax, .source ∘ .localSet, .source ∘ .localTee, Wasm.Lime1.Execution.values,
    .source .return_, .source .unreachable, .trap, fun t => [.invoke t.address], .frame, fun n => .label n []⟩

def coreAdmin : Syntax Core.Admin :=
  ⟨coreSyntax, .plain ∘ .localSet, .plain ∘ .localTee, coreValues, .plain .return_, .plain .unreachable, .trap,
    fun t => [.ref (.func t.address.value), .callRefType t.declaration.type.toDefType],
    fun n f => .frame n f.toCore, fun n => .label n []⟩

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (target : CallTarget) (q : Phase) :
    Wasm.V1.Execution.Config H := ⟨s, caller, q.render v1Admin target⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (target : CallTarget) (q : Phase) :
    Wasm.Lime1.Execution.Config H := ⟨s, caller, q.render limeAdmin target⟩

def coreConfig {H : Type} (s : Core.Store H) (caller : Frame) (target : CallTarget) (q : Phase) :
    Core.Config H := ⟨s, caller.toCore, q.render coreAdmin target⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph
