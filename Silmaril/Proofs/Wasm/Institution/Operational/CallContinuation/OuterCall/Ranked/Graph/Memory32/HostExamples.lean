module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.V1.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (AdminInstr Frame FuncAddr HostOutcome MemAddr MemInst ModuleInst Result Value)
open Wasm.V1.Execution

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private def slot : MemAddr := ⟨0⟩
private def wasmAddress : FuncAddr := ⟨1⟩
private def hostType : Wasm.V1.FuncType := ⟨[.int .i64, .int .i32], [.int .i32]⟩
private def wasmType : Wasm.V1.FuncType := ⟨[], [.int .i32]⟩
private def site : HostCall.V1.Site Nat := ⟨⟨0⟩, ⟨0⟩, hostType, 7⟩
private def fixed : FixedTable := ⟨⟨0⟩, ⟨[some wasmAddress], some 1⟩⟩
private def mod : ModuleInst :=
  { funcs := [site.address, wasmAddress], memories := [slot], tables := [fixed.address], types := [wasmType] }
private def fn : Function :=
  ⟨⟨mod, ⟨0⟩, [], [.int .i32], [.int .i32]⟩, 0, [], [.ranked (.numeric (.get ⟨0⟩))]⟩
private def program : Program := ⟨[none, some fn], some fixed⟩
private def caller : Frame := ⟨[i32 91], mod⟩
private def outer : Frame := ⟨[i32 14], {}⟩
private def memory : MemInst := ⟨⟨#[0xaa, 0, 0, 0, 0, 0xbb]⟩, none⟩
private def base : Store Nat :=
  { funcs := [.host hostType 7, .wasm fn.declaration.type fn.declaration.module fn.v1Func]
    tables := [fixed.table], memories := [memory] }
private def prior : ByteArray := ⟨#[0xaa, 0x55, 0, 0, 0, 0xbb]⟩
private def firstBytes : ByteArray := ⟨#[0xaa, 0x44, 0x33, 0x22, 0x11, 0xbb]⟩
private def secondBytes : ByteArray := ⟨#[0xaa, 0x99, 0x88, 0x77, 0x66, 0xbb]⟩
private def live : Store Nat := storeWithBytes base slot memory prior
private def firstStore : Store Nat := storeWithBytes live slot memory firstBytes
private def secondStore : Store Nat := storeWithBytes live slot memory secondBytes
private def saved : List Value := [i32 0]
private def args : List Value := [i64 81, i32 9]
private def load : Admin := .source ((Op.load 1).v1)
private def tail : List Admin := [.source (.localSet ⟨0⟩), load]
private def pending : Config Nat := site.pending live caller saved args tail

private theorem layout : Layout program base slot memory where
  memory := rfl
  functions := by
    intro address target found
    rcases address with ⟨_ | _ | _⟩ <;> simp [Program.lookup, program] at found
    subst target
    rfl
  table := by
    intro selected found
    change some fixed = some selected at found
    cases found
    rfl

private theorem graphChecked : program.checkV1 slot = true := rfl
private theorem siteChecked : site.Checked live caller args := ⟨rfl, rfl, rfl, by decide⟩

private inductive Outcome : HostOutcome Wasm.V1.Func Nat → Prop
  | first : Outcome (.returned firstStore (.values [i32 7]))
  | second : Outcome (.returned secondStore (.values [i32 8]))
  | trap : Outcome (.returned secondStore .trap)
  | diverge : Outcome .diverged

private def host : HostSemantics Nat :=
  fun target s given answer => target = 7 ∧ s = live ∧ given = args ∧ Outcome answer

private theorem contract : site.ReturnContract host (HostStoreEffect .fixed slot memory) live args := by
  rintro s r ⟨_, _, _, answer⟩
  cases answer with
  | first => exact ⟨rfl, prior, firstBytes, rfl, rfl, rfl⟩
  | second => exact ⟨rfl, prior, secondBytes, rfl, rfl, rfl⟩
  | trap => exact ⟨trivial, prior, secondBytes, rfl, rfl, rfl⟩

private theorem tailAllowed : CodeAllowedFor .fixed program slot .ranked 0 caller.module tail := by
  intro op member
  simp only [tail, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .source (.set ⟨0⟩)
  · exact .source (.load 1 rfl)

private theorem delivery {s : Store Nat} {r : Result} (answer : Outcome (.returned s r)) :
    Step host pending (HostCall.V1.resumed s caller saved tail r) :=
  (HostCall.V1.pending_step_iff (saved := saved) (tail := tail) siteChecked).mpr
    (.inl ⟨s, r, ⟨rfl, rfl, rfl, answer⟩, rfl⟩)

example : Step host pending pending :=
  (HostCall.V1.pending_step_iff (saved := saved) (tail := tail) siteChecked).mpr
    (.inr ⟨⟨rfl, rfl, rfl, .diverge⟩, rfl⟩)

example {dst : Config Nat} : ¬ Step CallFrame.v1NoHost pending dst := by
  intro move
  rcases (HostCall.V1.pending_step_iff (saved := saved) (tail := tail) siteChecked).mp move with
    ⟨_, _, impossible, _⟩ | ⟨impossible, _⟩
  · exact impossible
  · exact impossible

private def recorded (answer : BitVec 32) : Frame := { caller with locals := [i32 answer] }
private theorem callerReads {s : Store Nat} {mem : MemInst} {answer word : BitVec 32}
    (allocated : frameMemory s (recorded answer) = some (slot, mem))
    (read : MemoryQuery.EdgeAt mem.data 1 (.load 0) (.value word)) :
    Steps CallFrame.v1NoHost (HostCall.V1.resumed s caller saved tail (.values [i32 answer]))
      ⟨s, recorded answer, values [i32 word]⟩ := by
  have record : Step CallFrame.v1NoHost (HostCall.V1.resumed s caller saved tail (.values [i32 answer]))
      ⟨s, recorded answer, values saved ++ [load]⟩ :=
    .context (.localSet s caller ⟨0⟩ (i32 answer) (i32 91) rfl) saved [load]
  have loadStep := (MemoryWrite.v1_context_load_step_iff_at (host := CallFrame.v1NoHost) (immediate := immediate 1)
    (address := 0) (saved := []) (tail := []) allocated).mpr ⟨.value word, read, rfl⟩
  exact (Relation.ReflTransGen.single record).tail loadStep

private theorem readback {s : Store Nat} {r : Result} {dst : Config Nat}
    (answer : Outcome (.returned s r))
    (native : Steps CallFrame.v1NoHost (HostCall.V1.resumed s caller saved tail r) dst) :
    ∃ start out, Layout program s slot { memory with data := start.bytes } ∧
      Runs program slot start out ∧ dst = render base slot memory out := by
  obtain ⟨bytes, _, _, allocated, ready, eq⟩ := layout.host_return
    (mode := .fixed) (before := prior) rfl contract ⟨rfl, rfl, rfl, answer⟩
    (caller := caller) (saved := saved) tailAllowed
  obtain ⟨out, trace, _, output⟩ := (v1_run_iff graphChecked layout ready).mp (eq ▸ native)
  exact ⟨_, out, allocated, trace, output⟩

private def observedFirst : Config Nat := ⟨firstStore, recorded 7, values [i32 0x11223344]⟩
private def observedSecond : Config Nat := ⟨secondStore, recorded 8, values [i32 0x66778899]⟩
private theorem first : Steps CallFrame.v1NoHost
    (HostCall.V1.resumed firstStore caller saved tail (.values [i32 7])) observedFirst :=
  callerReads (show frameMemory firstStore (recorded 7) = some (slot, { memory with data := firstBytes }) from rfl)
    (MemoryQuery.fact_at (.load _ _ (by decide)))
private theorem second : Steps CallFrame.v1NoHost
    (HostCall.V1.resumed secondStore caller saved tail (.values [i32 8])) observedSecond :=
  callerReads (show frameMemory secondStore (recorded 8) = some (slot, { memory with data := secondBytes }) from rfl)
    (MemoryQuery.fact_at (.load _ _ (by decide)))

-- Each declared store can resume the same already checked caller tail.
example : Steps host pending observedFirst := .head (delivery .first) (Steps.of_internal first)
example : Steps host pending observedSecond := .head (delivery .second) (Steps.of_internal second)
example := readback Outcome.first first
example := readback Outcome.second second

-- Native lookup after each return still resolves through the fixed table to
-- the original allocated non-host body.
private theorem restoredDispatch {s : Store Nat} {r : Result} (answer : Outcome (.returned s r)) :
    CallResolution.Indirect.v1Resolve s caller ⟨0⟩ 0 = some (.resolved wasmAddress) := by
  have effect := (contract s r ⟨rfl, rfl, rfl, answer⟩).2
  obtain ⟨bytes, normalized, _, _, _⟩ := layout.host_store (mode := .fixed) (before := prior) rfl effect
  rw [normalized, layout.indirect_resolve (mode := .fixed) (calls := .ranked) graphChecked
    (fixed := fixed) rfl (f := caller) rfl bytes ⟨0⟩ 0]
  rfl

example := restoredDispatch Outcome.first
example := restoredDispatch Outcome.second
example := restoredDispatch Outcome.trap

private def wrap (cfg : Config Nat) : Config Nat :=
  ⟨cfg.store, outer, [.frame 1 cfg.frame [.label 1 [] cfg.code]]⟩
private def trapped : Config Nat := ⟨secondStore, outer, [.trap]⟩
private theorem unwind : Steps CallFrame.v1NoHost
    (wrap (HostCall.V1.resumed secondStore caller saved tail .trap)) trapped := by
  have discard := Step.frame (.label (.pure (host := CallFrame.v1NoHost) secondStore caller
    (.trapValues (i32 0) [] tail)) 1 []) 1 outer
  have close := Step.frame (.pure (host := CallFrame.v1NoHost) secondStore caller (.labelTrap 1 [])) 1 outer
  exact ((Relation.ReflTransGen.single discard).tail close).tail (.pure _ _ (.frameTrap 1 caller))

example : Steps host (wrap pending) trapped :=
  .head (.frame (.label (delivery .trap) 1 []) 1 outer) (Steps.of_internal unwind)

-- Restore the returned trap under the enclosing checked label and frame.
example : ∃ start out, Runs program slot start out ∧ trapped = render base slot memory out := by
  obtain ⟨bytes, _, _, _, ready, eq⟩ := layout.host_return
    (mode := .fixed) (before := prior) rfl contract ⟨rfl, rfl, rfl, Outcome.trap⟩
    (caller := caller) (saved := saved) tailAllowed
  let state : State := ⟨bytes, outer, [.frame 1 caller [.label 1 [] (values saved ++ [.trap] ++ tail)]]⟩
  have active : Ready program slot 1 memory.data.size state := by
    refine ⟨ready.1, ?_⟩
    intro item member
    change item ∈ [AdminInstr.frame 1 caller [.label 1 [] (values saved ++ [.trap] ++ tail)]] at member
    obtain rfl := List.mem_singleton.mp member
    refine .frame (address := wasmAddress) (fn := fn) rfl (by decide) rfl rfl ?_
    intro body h
    obtain rfl := List.mem_singleton.mp h
    exact .label (by decide) ready.2
  have lifted : wrap (HostCall.V1.resumed secondStore caller saved tail .trap) = render base slot memory state :=
    congrArg wrap eq
  obtain ⟨out, trace, _, rendered⟩ := (v1_run_iff graphChecked layout active).mp (lifted ▸ unwind)
  exact ⟨state, out, trace, rendered⟩

-- The contract rejects replacement of either linkage table while keeping a
-- valid scalar result and a legitimate write to the selected memory.
example : ¬ HostStoreEffect .fixed slot memory live { firstStore with funcs := [] } := by
  rintro ⟨priorBytes, bytes, _, _, eq⟩
  have length := congrArg (fun s : Store Nat => s.funcs.length) eq
  change 0 = 2 at length
  cases length

example : ¬ HostStoreEffect .fixed slot memory live { firstStore with tables := [] } := by
  rintro ⟨priorBytes, bytes, _, _, eq⟩
  have length := congrArg (fun s : Store Nat => s.tables.length) eq
  change 0 = 1 at length
  cases length

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
