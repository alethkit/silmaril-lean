module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Guard
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Native

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame FuncAddr MemAddr MemInst Value)
open Wasm.V1.Execution

theorem Layout.initial_store {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (layout : Layout p base m initial) : storeWithBytes base m initial initial.data = base :=
  RunProofs.initial_store layout

theorem call_ready {p : Program} {m : MemAddr} {addr : FuncAddr} {fn : Function}
    {caller : Frame} {index : FuncIdx} (found : p.lookup addr = some fn)
    (resolved : caller.module.funcs[index.toNat]? = some addr) (args : List Value) (bytes : ByteArray) :
    Ready p m (fn.rank + 1) bytes.size ⟨bytes, caller, values args ++ [.source (.call index)]⟩ :=
  RunProofs.initial_call found resolved args bytes

theorem Edge.module_eq {p : Program} {m : MemAddr} {src dst : State} (edge : Edge p m src dst) :
    dst.frame.module = src.frame.module :=
  RunProofs.edge_module edge

theorem Edge.extent_eq {p : Program} {m : MemAddr} {src dst : State} (edge : Edge p m src dst) :
    dst.bytes.size = src.bytes.size :=
  RunProofs.edge_extent edge

theorem Edge.ready {p : Program} {m : MemAddr} {src dst : State} {rank extent : Nat}
    (edge : Edge p m src dst) (checked : p.checkV1 m = true) (ready : Ready p m rank extent src) :
    Ready p m rank extent dst :=
  ⟨edge.extent_eq.trans ready.1, RunProofs.preserve checked edge ready.2⟩

theorem render_shared {H : Type} {p : Program} {m : MemAddr} {base : Store H}
    {initial : MemInst} {src : State} {rank : Nat} (ready : Ready p m rank initial.data.size src) :
    SharedStore base m initial (render base m initial src).store :=
  ⟨src.bytes, ready.1, rfl⟩

/-- Exact native successors, including each separate administrative trap step. -/
theorem v1_step_iff {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : p.checkV1 m = true) (layout : Layout p base m initial) {src : State} {rank : Nat}
    (ready : Ready p m rank initial.data.size src) {dst : Config H} :
    Step CallFrame.v1NoHost (render base m initial src) dst ↔
      ∃ out, Edge p m src out ∧ Ready p m rank initial.data.size out ∧ dst = render base m initial out :=
  RunProofs.step_iff checked layout ready

/-- Each finite native prefix reflects to a run whose exact store, locals and
administrative code render the endpoint. The endpoint need not have returned. -/
theorem v1_run_iff {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : p.checkV1 m = true) (layout : Layout p base m initial) {src : State} {rank : Nat}
    (ready : Ready p m rank initial.data.size src) {dst : Config H} :
    Steps CallFrame.v1NoHost (render base m initial src) dst ↔
      ∃ out, Runs p m src out ∧ Ready p m rank initial.data.size out ∧ dst = render base m initial out :=
  RunProofs.run_iff checked layout ready

/-- Ordinary entry from an external caller resolving a checked root. -/
theorem v1_call_run_iff {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : p.checkV1 m = true) (layout : Layout p base m initial)
    {root : FuncAddr} {fn : Function} {caller : Frame} {index : FuncIdx} {args : List Value}
    (found : p.lookup root = some fn) (resolved : caller.module.funcs[index.toNat]? = some root)
    {dst : Config H} :
    Steps CallFrame.v1NoHost ⟨base, caller, values args ++ [.source (.call index)]⟩ dst ↔
      ∃ out, Runs p m ⟨initial.data, caller, values args ++ [.source (.call index)]⟩ out ∧
        Ready p m (fn.rank + 1) initial.data.size out ∧ dst = render base m initial out := by
  have exactRun := v1_run_iff (dst := dst) checked layout (call_ready found resolved args initial.data)
  simpa only [render, layout.initial_store] using exactRun

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
