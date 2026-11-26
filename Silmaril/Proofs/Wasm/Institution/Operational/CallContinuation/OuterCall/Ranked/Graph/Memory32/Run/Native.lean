module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Guard
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.RunProofs

open Execution.Runtime (Frame FuncAddr MemAddr MemInst ModuleInst Value)
open Wasm.V1.Execution

private theorem selected {H : Type} {p : Program} {base : Store H} {m : MemAddr} {initial : MemInst}
    (layout : Layout p base m initial) {f : Frame} (slot : f.module.memories[0]? = some m) (bytes : ByteArray) :
    frameMemory (storeWithBytes base m initial bytes) f = some (m, { initial with data := bytes }) := by
  have before : frameMemory base f = some (m, initial) := by
    simp [frameMemory, slot, layout.memory]
  exact MemoryWrite.v1_frameMemory_setBytes before bytes

private theorem update_bytes {H : Type} (base : Store H) (m : MemAddr) (initial : MemInst)
    (before after : ByteArray) :
    setMemory (storeWithBytes base m initial before) m { initial with data := after } =
      storeWithBytes base m initial after := by
  simp [storeWithBytes, setMemory, List.set_set]

theorem sound {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : p.checkV1 m = true) (layout : Layout p base m initial) {src dst : State}
    (move : Edge p m src dst) :
    Step CallFrame.v1NoHost (render base m initial src) (render base m initial dst) := by
  induction move with
  | pure move => exact .pure _ _ move
  | context move saved tail ih => exact .context ih saved tail
  | label move n ih => exact .label ih n []
  | frame move n outer ih => exact .frame ih n outer
  | get found => exact .localGet _ _ _ _ found
  | set found => exact .localSet _ _ _ _ _ found
  | resolve found => exact .call _ _ _ _ found
  | @enter bytes f address fn args found count =>
    exact .invokeWasm _ _ address fn.declaration.type fn.declaration.module fn.v1Func args
      (layout.functions address fn found) count (p.function_checked checked found).1
  | load slot rule =>
    exact (MemoryWrite.v1_context_load_step_iff_at (saved := []) (tail := []) (selected layout slot _)).mpr
      ⟨_, rule, by simp [render, values]⟩
  | store slot rule =>
    have native := (MemoryWrite.v1_context_store_step_iff_at (host := CallFrame.v1NoHost) (saved := []) (tail := [])
      (selected layout slot _)).mpr ⟨_, rule, rfl⟩
    simpa [render, MemoryWrite.v1ConfigAt, values, update_bytes, value, Value.int] using native
  | storeTrap slot rule =>
    exact (MemoryWrite.v1_context_store_step_iff_at (saved := []) (tail := [])
      (selected layout slot _)).mpr ⟨_, rule, rfl⟩

private theorem reflect_load {H : Type} {p : Program} {m : MemAddr} {base : Store H}
    {initial : MemInst} (layout : Layout p base m initial)
    {bytes : ByteArray} {f : Frame} {arg : Wasm.V1.MemArg} {ptr : BitVec 32} {dst : Config H}
    (slot : f.module.memories[0]? = some m)
    (move : Step CallFrame.v1NoHost
      (render base m initial ⟨bytes, f, MemoryQuery.v1CodeAt arg (.load ptr)⟩) dst) :
    ∃ out, Edge p m ⟨bytes, f, MemoryQuery.v1CodeAt arg (.load ptr)⟩ out ∧
      dst = render base m initial out := by
  obtain ⟨out, edge, eq⟩ := (MemoryWrite.v1_context_load_step_iff_at (saved := []) (tail := [])
    (selected layout slot _)).mp move
  exact ⟨_, .load slot edge, by simpa [render, values] using eq⟩

private theorem reflect_store {H : Type} {p : Program} {m : MemAddr} {base : Store H}
    {initial : MemInst} (layout : Layout p base m initial)
    {bytes : ByteArray} {f : Frame} {arg : Wasm.V1.MemArg} {ptr word : BitVec 32} {dst : Config H}
    (slot : f.module.memories[0]? = some m)
    (move : Step CallFrame.v1NoHost (render base m initial ⟨bytes, f,
      [value (.int .i32 ptr), value (.int .i32 word), .source (.intStore .i32 none arg)]⟩) dst) :
    ∃ out, Edge p m ⟨bytes, f,
      [value (.int .i32 ptr), value (.int .i32 word), .source (.intStore .i32 none arg)]⟩ out ∧
      dst = render base m initial out := by
  obtain ⟨out, edge, eq⟩ := (MemoryWrite.v1_context_store_step_iff_at (saved := []) (tail := [])
    (immediate := arg) (address := ptr) (word := word) (selected layout slot _)).mp move
  cases MemoryWrite.invert_at edge with
  | write => exact ⟨_, .store slot edge, by simpa [render, MemoryWrite.v1ConfigAt, values, update_bytes] using eq⟩
  | trap => exact ⟨_, .storeTrap slot edge, eq⟩

private theorem source_last {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst}
    {code : List Admin} {op : Wasm.V1.Instr}
    (guard : CodeAllowed p m rank mod code) (last : code.getLast? = some (.source op)) :
    SourceAllowed p m rank mod op :=
  source_allowed (guard _ (List.mem_of_getLast? last))

theorem readback {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (layout : Layout p base m initial) {src dst : Config H} (move : Step CallFrame.v1NoHost src dst)
    (bytes : ByteArray) (same : src.store = storeWithBytes base m initial bytes)
    {rank : Nat} (ready : CodeAllowed p m rank src.frame.module src.code) :
    ∃ out, Edge p m ⟨bytes, src.frame, src.code⟩ out ∧ dst = render base m initial out := by
  induction move generalizing bytes rank with
  | pure s f move => exact ⟨_, .pure move, by simp [render, ← same]⟩
  | @context s t f g before after move saved tail ih =>
    have leading := ((append_allowed (l := values saved ++ before) (r := tail)).mp ready).1
    have inside := ((append_allowed (l := values saved) (r := before)).mp leading).2
    obtain ⟨next, rule, eq⟩ := ih bytes same inside
    exact ⟨_, .context rule saved tail, congrArg
      (fun c : Config H => (⟨c.store, c.frame, values saved ++ c.code ++ tail⟩ : Config H)) eq⟩
  | label move n cont ih =>
    have guard := single_allowed.mp ready
    cases guard with | label _ inside =>
      obtain ⟨next, rule, eq⟩ := ih bytes same inside
      exact ⟨_, .label rule n, congrArg
        (fun c : Config H => (⟨c.store, c.frame, [.label n [] c.code]⟩ : Config H)) eq⟩
  | frame move n outer ih =>
    have guard := single_allowed.mp ready
    cases guard with | frame found smaller scope arity inside =>
      obtain ⟨next, rule, eq⟩ := ih bytes same inside
      exact ⟨_, .frame rule n outer, congrArg
        (fun c : Config H => (⟨c.store, outer, [.frame n c.frame c.code]⟩ : Config H)) eq⟩
  | localGet s f i v found => exact ⟨_, .get found, by simp [render, ← same]⟩
  | localSet s f i v old found => exact ⟨_, .set found, by simp [render, ← same]⟩
  | call s f i address found => exact ⟨_, .resolve found, by simp [render, ← same]⟩
  | invokeWasm s f address ty mod fn args found count arity =>
    have guard := single_allowed.mp (append_allowed.mp ready).2
    cases guard with
    | invoke declared smaller =>
      change s = storeWithBytes base m initial bytes at same
      rw [same] at found
      change base.funcs[address.value]? = some (.wasm ty mod fn) at found
      rw [layout.functions address _ declared] at found
      obtain ⟨rfl, rfl, rfl⟩ := Execution.Runtime.FuncInst.wasm.inj (Option.some.inj found)
      exact ⟨_, .enter declared count, by simp [render, ← same, Declaration.frame, Function.v1Func, Declaration.type]⟩
  | invokeHost s t f address ty fn args r found count behavior => cases behavior
  | invokeHostDiverges s f address ty fn args found count behavior => cases behavior
  | intLoad s f t packed arg ptr a mem v found loaded =>
    have guard := source_last ready (op := .intLoad t packed arg) rfl
    cases guard with | load offset slot =>
      change s = storeWithBytes base m initial bytes at same
      change f.module.memories[0]? = some m at slot
      have foundNow := selected layout slot bytes
      rw [same, foundNow] at found
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      subst s
      exact reflect_load layout slot (.intLoad _ _ _ _ _ _ _ _ _ foundNow loaded)
  | intLoadTrap s f t packed arg ptr a mem found loaded =>
    have guard := source_last ready (op := .intLoad t packed arg) rfl
    cases guard with | load offset slot =>
      change s = storeWithBytes base m initial bytes at same
      change f.module.memories[0]? = some m at slot
      have foundNow := selected layout slot bytes
      rw [same, foundNow] at found
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      subst s
      exact reflect_load layout slot (.intLoadTrap _ _ _ _ _ _ _ _ foundNow loaded)
  | intStore s f t packed arg ptr word a mem written found stored =>
    have guard := source_last ready (op := .intStore t packed arg) rfl
    cases guard with | store offset slot =>
      change s = storeWithBytes base m initial bytes at same
      change f.module.memories[0]? = some m at slot
      have foundNow := selected layout slot bytes
      rw [same, foundNow] at found
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      subst s
      exact reflect_store layout slot (.intStore _ _ _ _ _ _ _ _ _ _ foundNow stored)
  | intStoreTrap s f t packed arg ptr word a mem found stored =>
    have guard := source_last ready (op := .intStore t packed arg) rfl
    cases guard with | store offset slot =>
      change s = storeWithBytes base m initial bytes at same
      change f.module.memories[0]? = some m at slot
      have foundNow := selected layout slot bytes
      rw [same, foundNow] at found
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      subst s
      exact reflect_store layout slot (.intStoreTrap _ _ _ _ _ _ _ _ _ foundNow stored)
  | _ =>
    have guard := source_last ready rfl
    cases guard

theorem initial_store {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (layout : Layout p base m initial) :
    storeWithBytes base m initial initial.data = base := by
  obtain ⟨_, allocated⟩ := List.getElem?_eq_some_iff.mp layout.memory
  change setMemory base m initial = base
  unfold setMemory
  rw [← allocated, List.set_getElem_self]

theorem step_iff {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : p.checkV1 m = true) (layout : Layout p base m initial) {src : State} {rank : Nat}
    (ready : Ready p m rank initial.data.size src) {dst : Config H} :
    Step CallFrame.v1NoHost (render base m initial src) dst ↔
      ∃ out, Edge p m src out ∧ Ready p m rank initial.data.size out ∧ dst = render base m initial out := by
  constructor
  · intro step
    obtain ⟨out, edge, eq⟩ := readback layout step src.bytes rfl ready.2
    exact ⟨out, edge, ⟨(edge_extent edge).trans ready.1, preserve checked edge ready.2⟩, eq⟩
  · rintro ⟨out, edge, _, rfl⟩
    exact sound checked layout edge

theorem run_iff {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : p.checkV1 m = true) (layout : Layout p base m initial) {src : State} {rank : Nat}
    (ready : Ready p m rank initial.data.size src) {dst : Config H} :
    Steps CallFrame.v1NoHost (render base m initial src) dst ↔
      ∃ out, Runs p m src out ∧ Ready p m rank initial.data.size out ∧ dst = render base m initial out := by
  constructor
  · intro run
    induction run with
    | refl => exact ⟨src, .refl, ready, rfl⟩
    | tail _ step ih =>
      obtain ⟨middle, trace, guarded, rfl⟩ := ih
      obtain ⟨next, edge, nextGuarded, eq⟩ := (step_iff checked layout guarded).mp step
      exact ⟨next, trace.tail edge, nextGuarded, eq⟩
  · rintro ⟨out, trace, _, rfl⟩
    exact Relation.ReflTransGen.lift (render base m initial) (fun _ _ h => sound checked layout h) _ _ trace

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.RunProofs
