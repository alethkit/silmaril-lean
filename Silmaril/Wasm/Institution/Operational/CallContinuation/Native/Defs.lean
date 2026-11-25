module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Defs
public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation

open Execution
open Execution.Runtime (Frame FuncAddr Value)

def tail {A : Type} (nop : A) (hasTail : Bool) : List A :=
  if hasTail then [nop] else []

def render {A : Type} (nop trap : A) (values : List Value → List A)
    (call : CallFrame.State → List A) : State → List A
  | .active q => call q ++ [nop]
  | .resume stack => values stack ++ [nop]
  | .done stack => values stack
  | .trapped stack hasTail => values stack ++ [trap] ++ tail nop hasTail

def v1Code (addr : FuncAddr) (fn : CallFrame.Callee) : State → List Wasm.V1.Execution.Admin :=
  render (.source .nop) .trap Wasm.V1.Execution.values (CallFrame.v1Code addr fn)

def limeCode (addr : FuncAddr) (fn : CallFrame.Callee) : State → List Wasm.Lime1.Execution.Admin :=
  render (.source .nop) .trap Wasm.Lime1.Execution.values (CallFrame.limeCode addr fn)

def coreCode (addr : FuncAddr) (fn : CallFrame.Callee) : State → List Core.Admin :=
  render (.plain .nop) .trap (fun stack => Core.vals (stack.map Value.toCore)) (CallFrame.coreCode addr fn)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame)
    (addr : FuncAddr) (fn : CallFrame.Callee) (q : State) : Wasm.V1.Execution.Config H :=
  ⟨s, caller, v1Code addr fn q⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame)
    (addr : FuncAddr) (fn : CallFrame.Callee) (q : State) : Wasm.Lime1.Execution.Config H :=
  ⟨s, caller, limeCode addr fn q⟩

def coreConfig {H : Type} (s : Core.Store H) (caller : Frame)
    (addr : FuncAddr) (fn : CallFrame.Callee) (q : State) : Core.Config H :=
  ⟨s, caller.toCore, coreCode addr fn q⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation
