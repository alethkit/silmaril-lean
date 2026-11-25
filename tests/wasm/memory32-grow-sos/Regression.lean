module

import Silmaril.Wasm.Institution.Operational.MemoryGrow.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame MemAddr MemInst)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Institution.Operational.MemoryGrow

private def firstPage : ByteArray := ⟨Array.replicate Memory.pageSize 0x5a⟩
private def secondPage : ByteArray := ⟨Array.replicate Memory.pageSize 0⟩
private def mine : MemInst := ⟨firstPage, some 2⟩
private def other : MemInst := ⟨.empty, none⟩
private def address : MemAddr := ⟨1⟩
private def frame : Frame := ⟨[.int .i64 7], { memories := [address] }⟩
private def store : V1.Execution.Store Unit := { memories := [other, mine] }
private abbrev limeStore := store.mapCode V1.Func.toLime
private def v1Host : V1.Execution.HostSemantics Unit := fun _ _ _ _ => False
private def limeHost : Lime1.Execution.HostSemantics Unit := fun _ _ _ _ => False
private def coreHost : Core.HostSemantics Unit := fun _ _ _ _ => False

private theorem sizeMine : mine.data.size = Memory.pageSize := by
  change (Array.replicate Memory.pageSize (0x5a : UInt8)).size = _
  simp

private theorem good : Admitted mine := by
  constructor
  · rw [sizeMine, Nat.mod_self]
  · intro limit eq
    have same : limit = 2 := Option.some.inj eq.symm
    subst limit
    decide

private theorem found : V1.Execution.frameMemory store frame = some (address, mine) := rfl
private theorem limeFound : Lime1.Execution.frameMemory limeStore frame = some (address, mine) :=
  (V1.Execution.map_frameMemory store frame).trans found
private theorem coreFound :
    limeStore.toCore.mem? frame.toCore MemoryQuery.index = some (address.value, mine.toCore) :=
  MemoryQuery.memory_toCore limeFound

private theorem canGrow : Memory.grow? mine.data mine.max 1 = some (firstPage ++ secondPage) := by
  unfold Memory.grow?
  have aligned := good.aligned
  have within : Memory.size mine.data = 1 := by simp [Memory.size, sizeMine, Memory.pageSize]
  rw [ite_eq_left]
  · rfl
  · rw [within]
    exact ⟨aligned, by decide, Or.inr (by decide)⟩

private theorem one : Edge mine (.request 1) (.grown (firstPage ++ secondPage)) :=
  fact (.grow 1 _ canGrow)

example : Memory.size (firstPage ++ secondPage) = 2 :=
  (grown_pages one).trans (by simp [Memory.size, sizeMine, Memory.pageSize])

example : V1.Execution.Step v1Host (v1Config store frame address mine (.request 1))
    (v1Config store frame address mine (.grown (firstPage ++ secondPage))) :=
  v1_sound found one

example : (v1Config store frame address mine (.grown (firstPage ++ secondPage))).store.memories =
    [other, { mine with data := firstPage ++ secondPage }] := rfl

example : Lime1.Execution.Step limeHost (v1Config store frame address mine (.request 1)).toLime
    (v1Config store frame address mine .failed).toLime := by
  rw [v1_to_lime, v1_to_lime]
  exact lime_sound limeFound (fact (.fail 1))

example : (coreConfig limeStore.toCore frame.toCore address.value mine .failed).code =
    [.plain (.intConst .i32 0xffffffff)] := rfl

example : Core.Step Numerics.Profile.spec coreHost (v1Config store frame address mine (.request 1)).toLime.toCore
    (v1Config store frame address mine (.grown (firstPage ++ secondPage))).toLime.toCore := by
  rw [v1_to_lime, v1_to_lime, lime_to_core, lime_to_core]
  exact core_sound good coreFound one

private theorem beyondLimit : Memory.grow? mine.data mine.max 2 = none := by
  unfold Memory.grow?
  have within : Memory.size mine.data = 1 := by simp [Memory.size, sizeMine, Memory.pageSize]
  simp only [good.aligned, within, true_and]
  rfl

example {target : Core.Config Unit} (h : Core.Step Numerics.Profile.spec coreHost
    (coreConfig limeStore.toCore frame.toCore address.value mine (.request 2)) target) :
    target = coreConfig limeStore.toCore frame.toCore address.value mine .failed := by
  obtain ⟨out, edge, eq⟩ := (core_step_iff good coreFound).mp h
  cases invert edge with
  | grow _ _ grew =>
    change Memory.grow? mine.data mine.max 2 = _ at grew
    rw [beyondLimit] at grew
    contradiction
  | fail => exact eq
