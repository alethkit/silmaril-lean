module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.Nested

open Execution
open Execution.Runtime (Frame FuncAddr Value)

def resultCode {A : Type} (values : List Value → List A) (trap : A) : Result → List A
  | .values stack => values stack
  | .trap => [trap]

def render {A : Type} (label frame : List A → A) (result : Result → List A)
    (body : CallContinuation.State → List A) : State → List A
  | .label q => [frame [label (body q)]]
  | .exit out => [frame (result out)]
  | .done out => result out

def v1Code (outer : Frame) (addr : FuncAddr) (fn : CallFrame.Callee) (arity : Nat) :
    State → List Wasm.V1.Execution.Admin :=
  render (.label arity []) (.frame arity outer)
    (resultCode Wasm.V1.Execution.values .trap) (CallContinuation.v1Code addr fn)

def limeCode (outer : Frame) (addr : FuncAddr) (fn : CallFrame.Callee) (arity : Nat) :
    State → List Wasm.Lime1.Execution.Admin :=
  render (.label arity []) (.frame arity outer)
    (resultCode Wasm.Lime1.Execution.values .trap) (CallContinuation.limeCode addr fn)

def coreCode (outer : Frame) (addr : FuncAddr) (fn : CallFrame.Callee) (arity : Nat) :
    State → List Core.Admin :=
  render (.label arity []) (.frame arity outer.toCore)
    (resultCode (fun stack => Core.vals (stack.map Value.toCore)) .trap) (CallContinuation.coreCode addr fn)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (caller outer : Frame)
    (addr : FuncAddr) (fn : CallFrame.Callee) (arity : Nat) (q : State) : Wasm.V1.Execution.Config H :=
  ⟨s, caller, v1Code outer addr fn arity q⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller outer : Frame)
    (addr : FuncAddr) (fn : CallFrame.Callee) (arity : Nat) (q : State) : Wasm.Lime1.Execution.Config H :=
  ⟨s, caller, limeCode outer addr fn arity q⟩

def coreConfig {H : Type} (s : Core.Store H) (caller outer : Frame)
    (addr : FuncAddr) (fn : CallFrame.Callee) (arity : Nat) (q : State) : Core.Config H :=
  ⟨s, caller.toCore, coreCode outer addr fn arity q⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.Nested
