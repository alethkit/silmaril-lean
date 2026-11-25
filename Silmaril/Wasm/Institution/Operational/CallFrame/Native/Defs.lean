module

public import Silmaril.Wasm.Institution.Operational.CallFrame.Defs
public import Silmaril.Wasm.Institution.Operational.Locals.Native.Defs
public import Silmaril.Wasm.Versions.Lime1.Runtime.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallFrame

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (AdminInstr Frame FuncAddr Value)

def Program.instructions {I : Type} (emit : Locals.Op → I) (ret unreachable : I) :
    Program → List I
  | .locals code => code.map emit
  | .ret stack => (Locals.values stack).map emit ++ [ret]
  | .unreachable => [unreachable]

def Callee.type (fn : Callee) : Wasm.V1.FuncType :=
  ⟨fn.params, fn.result.toList⟩

def Callee.v1Func (fn : Callee) : Wasm.V1.Func :=
  ⟨fn.typeIndex, fn.locals, fn.program.instructions Locals.v1Instr .return_ .unreachable⟩

def Callee.limeFunc (fn : Callee) : Wasm.Lime1.Func :=
  ⟨fn.typeIndex, fn.locals, fn.program.instructions Locals.limeInstr .return_ .unreachable⟩

def Callee.coreFunc (fn : Callee) : Func :=
  ⟨fn.typeIndex, fn.locals.map Wasm.V1.ValType.toCore,
    fn.program.instructions Locals.coreInstr .return_ .unreachable⟩

def Callee.coreInstance {H : Type} (fn : Callee) : Core.FuncInst H :=
  ⟨fn.type.toDefType, fn.module.toCore, .wasm fn.coreFunc⟩

def Callee.frame (fn : Callee) (ls : List Value) : Frame := ⟨ls, fn.module⟩


def legacyBody {I : Type} (emit : Locals.Op → I) (ret unreachable : I) : Body → List (AdminInstr I)
  | .code p => (p.instructions emit ret unreachable).map AdminInstr.source
  | .trap => [.trap]

def legacyExit {I : Type} (value : Value → AdminInstr I) (ret : I) : Exit → List (AdminInstr I)
  | .values stack => stack.map value
  | .ret stack => stack.map value ++ [.source ret]
  | .trap => [.trap]

/-- V1 and Lime1 share their administrative configuration and runtime value types. -/
def legacyCode {I : Type} (emit : Locals.Op → I) (value : Value → AdminInstr I)
    (ret unreachable : I) (address : FuncAddr) (fn : Callee) : State → List (AdminInstr I)
  | .invoke saved args => (saved ++ args).map value ++ [.invoke address]
  | .label saved ls body =>
      saved.map value ++ [.frame fn.arity (fn.frame ls)
        [.label fn.arity [] (legacyBody emit ret unreachable body)]]
  | .exit saved ls ready =>
      saved.map value ++ [.frame fn.arity (fn.frame ls) (legacyExit value ret ready)]
  | .returned saved results => (saved ++ results).map value
  | .trapped saved => saved.map value ++ [.trap]

def v1Code (address : FuncAddr) (fn : Callee) : State → List Wasm.V1.Execution.Admin :=
  legacyCode Locals.v1Instr Wasm.V1.Execution.value .return_ .unreachable address fn

def limeCode (address : FuncAddr) (fn : Callee) : State → List Wasm.Lime1.Execution.Admin :=
  legacyCode Locals.limeInstr Wasm.Lime1.Execution.value .return_ .unreachable address fn

def coreBody : Body → List Core.Admin
  | .code p => Core.expression (p.instructions Locals.coreInstr .return_ .unreachable)
  | .trap => [.trap]

def coreExit : Exit → List Core.Admin
  | .values stack => Core.vals (stack.map Value.toCore)
  | .ret stack => Core.vals (stack.map Value.toCore) ++ [.plain .return_]
  | .trap => [.trap]

def coreCode (address : FuncAddr) (fn : Callee) : State → List Core.Admin
  | .invoke saved args =>
      Core.vals ((saved ++ args).map Value.toCore) ++ [.ref (.func address.value), .callRefType fn.type.toDefType]
  | .label saved ls body =>
      Core.vals (saved.map Value.toCore) ++
        [.frame fn.arity (fn.frame ls).toCore [.label fn.arity [] (coreBody body)]]
  | .exit saved ls ready =>
      Core.vals (saved.map Value.toCore) ++ [.frame fn.arity (fn.frame ls).toCore (coreExit ready)]
  | .returned saved results => Core.vals ((saved ++ results).map Value.toCore)
  | .trapped saved => Core.vals (saved.map Value.toCore) ++ [.trap]

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame)
    (address : FuncAddr) (fn : Callee) (q : State) : Wasm.V1.Execution.Config H :=
  ⟨s, caller, v1Code address fn q⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame)
    (address : FuncAddr) (fn : Callee) (q : State) : Wasm.Lime1.Execution.Config H :=
  ⟨s, caller, limeCode address fn q⟩

def coreConfig {H : Type} (s : Core.Store H) (caller : Frame)
    (address : FuncAddr) (fn : Callee) (q : State) : Core.Config H :=
  ⟨s, caller.toCore, coreCode address fn q⟩

abbrev v1NoHost {H : Type} : Wasm.V1.Execution.HostSemantics H := fun _ _ _ _ => False
abbrev limeNoHost {H : Type} : Wasm.Lime1.Execution.HostSemantics H := fun _ _ _ _ => False

end Silmaril.Wasm.Institution.Operational.CallFrame
