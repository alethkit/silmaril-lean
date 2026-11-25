module

public import Silmaril.Wasm.Execution.Runtime

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall

open Execution.Runtime (Frame ModuleInst FuncAddr Value)

/-- The static part of an allocated, numeric Wasm function. -/
structure Declaration where
  module : ModuleInst
  typeIndex : TypeIdx
  params : List NumType
  locals : List NumType
  results : List NumType

def Declaration.type (decl : Declaration) : Wasm.V1.FuncType := ⟨decl.params, decl.results⟩

def Declaration.frame (decl : Declaration) (args : List Value) : Frame :=
  ⟨args ++ decl.locals.map Value.zero, decl.module⟩

/-- The direct-call descriptor is independent of the argument values and the
proof of the target body. It can be shared by a table of checked declarations. -/
structure CallTarget where
  index : FuncIdx
  address : FuncAddr
  declaration : Declaration

def CallTarget.Resolves (target : CallTarget) (caller : Frame) : Prop :=
  caller.module.funcs[target.index.toNat]? = some target.address

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall
