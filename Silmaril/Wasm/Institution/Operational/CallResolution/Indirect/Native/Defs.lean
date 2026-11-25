module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect

open Execution.Runtime (FuncAddr Frame Value)
open Execution.Core (Admin Ref constI32)
open Wasm.Lime1.Execution (values)

def tableIndex : TableIdx := ⟨0⟩

def Site.coreCast (site : Site) : Admin :=
  .plain (.refCast ⟨true, .typeIdx site.typeIndex⟩)

def Site.coreCall (site : Site) : Admin :=
  .plain (.callRef site.typeIndex)

def coreRef (entry : Option FuncAddr) : Ref :=
  (entry.map fun addr => .func addr.value).getD .null

def Site.coreCode (site : Site) (selector : BitVec 32) : Phase → List Admin
  | .start => [constI32 selector, .plain (.callIndirect tableIndex site.typeIndex)]
  | .lookup => [constI32 selector, .plain (.tableGet tableIndex), site.coreCast, site.coreCall]
  | .cast entry => [.ref (coreRef entry), site.coreCast, site.coreCall]
  | .call entry => [.ref (coreRef entry), site.coreCall]
  | .boundsTrap => [.trap, site.coreCast, site.coreCall]
  | .mismatchTrap => [.trap, site.coreCall]
  | .nullTrap => [.trap]

def coreConfig {H : Type} (s : Execution.Core.Store H) (caller : Frame)
    (site : Site) (selector : BitVec 32) (stack : List Value) (rest : List Admin) (phase : Phase) :
    Execution.Core.Config H :=
  ⟨s, caller.toCore, Execution.Core.vals (stack.map Value.toCore) ++ site.coreCode selector phase ++ rest⟩

def limeSource {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame)
    (site : Site) (selector : BitVec 32) (stack : List Value) (rest : List Wasm.Lime1.Execution.Admin) :
    Wasm.Lime1.Execution.Config H :=
  ⟨s, caller, values (stack ++ [Value.int .i32 selector]) ++ .source (.callIndirect site.typeIndex) :: rest⟩

def limeResolved {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame)
    (stack : List Value) (rest : List Wasm.Lime1.Execution.Admin) (out : Outcome) : Wasm.Lime1.Execution.Config H :=
  ⟨s, caller, values stack ++ (match out with | .resolved addr => .invoke addr | _ => .trap) :: rest⟩

open CallContinuation.OuterCall.Ranked.Graph (Function)

/-- Each consulted nonnull table entry has its exact checked graph function.
Other registrations do not participate in this lookup. -/
def Site.CoreAllocated {H : Type} (site : Site) (program : CallContinuation.OuterCall.Ranked.Graph.Program)
    (s : Execution.Core.Store H) : Prop :=
  ∀ address fn, some address ∈ site.table.refs → program.lookup address = some fn →
    s.funcs[address.value]? = some fn.coreInstance

def Site.LimeAllocated {H : Type} (site : Site) (program : CallContinuation.OuterCall.Ranked.Graph.Program)
    (s : Wasm.Lime1.Execution.Store H) : Prop :=
  ∀ address fn, some address ∈ site.table.refs → program.lookup address = some fn →
    s.funcs[address.value]? = some (.wasm fn.declaration.type fn.declaration.module fn.limeFunc)


def coreEntered {H : Type} (s : Execution.Core.Store H) (caller : Frame)
    (fn : Function) (saved args : List Value) (rest : List Admin) : Execution.Core.Config H :=
  ⟨s, caller.toCore, Execution.Core.vals (saved.map Value.toCore) ++
    .frame fn.declaration.type.results.length (fn.declaration.frame args).toCore
      [.label fn.declaration.type.results.length [] (Execution.Core.expression fn.coreFunc.body)] :: rest⟩

def limeEntered {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame)
    (fn : Function) (saved args : List Value) (rest : List Wasm.Lime1.Execution.Admin) :
    Wasm.Lime1.Execution.Config H :=
  ⟨s, caller, values saved ++ .frame fn.declaration.type.results.length (fn.declaration.frame args)
    [.label fn.declaration.type.results.length [] (Wasm.Lime1.Execution.expression fn.limeFunc.body)] :: rest⟩

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect
