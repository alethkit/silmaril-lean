module

import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Institution.Operational.MemoryWrite
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Logic.Core (bytesAt Region)

private def original : ByteArray := ⟨#[0xaa, 0, 0, 0, 0, 0xbb]⟩
private def changed : ByteArray := ⟨#[0xaa, 0x44, 0x33, 0x22, 0x11, 0xbb]⟩
private def other : Runtime.MemInst := ⟨⟨#[7, 8]⟩, none⟩
private def mem : Runtime.MemInst := ⟨original, some 3⟩
private def addr : Runtime.MemAddr := ⟨1⟩
private def frame : Runtime.Frame := ⟨[.int .i64 9], { memories := [addr] }⟩
private def store : V1.Execution.Store Unit := { memories := [other, mem] }
private def host : V1.Execution.HostSemantics Unit := fun _ _ _ _ => False
private def limeHost : Lime1.Execution.HostSemantics Unit := fun _ _ _ _ => False

private theorem found : V1.Execution.frameMemory store frame = some (addr, mem) := rfl
private theorem limeFound :
    Lime1.Execution.frameMemory (store.mapCode V1.Func.toLime) frame = some (addr, mem) :=
  (V1.Execution.map_frameMemory store frame).trans found

private theorem write : Edge original (.store 1 0x11223344) (.written changed) :=
  fact (.write 1 0x11223344 changed (by decide))

private theorem oob : Edge original (.store 3 0x11223344) .trap :=
  fact (.trap 3 0x11223344 (by decide))

example : Memory.load changed 1 4 = some 0x11223344 := read_after_write write
example : bytesAt changed ⟨5, 1⟩ = bytesAt original ⟨5, 1⟩ :=
  disjoint_bytes write (Or.inl (show (1 : Nat) + 4 ≤ 5 from by decide))

example : V1.Execution.Step host (v1Config store frame addr mem (.store 1 0x11223344))
    (v1Config store frame addr mem (.written changed)) :=
  v1_sound found write

example : (v1Config store frame addr mem (.written changed)).store.memories =
    [other, { mem with data := changed }] := rfl

example : Lime1.Execution.Step limeHost
    (v1Config store frame addr mem (.store 3 0x11223344)).toLime
    (v1Config store frame addr mem .trap).toLime := by
  rw [v1_to_lime, v1_to_lime]
  exact lime_sound limeFound oob

example : (v1Config store frame addr mem .trap).store = store := rfl

example : Core.Step Numerics.Profile.spec noHost
    (v1Config store frame addr mem (.store 1 0x11223344)).toLime.toCore
    (v1Config store frame addr mem (.written changed)).toLime.toCore := by
  rw [v1_to_lime, v1_to_lime,
    lime_to_core _ _ _ _ (show Admitted original (.store 1 0x11223344) from trivial),
    lime_to_core _ _ _ _ (closed write)]
  exact core_sound (memory32_toCore limeFound) write

example {target : Core.Config Unit}
    (h : Core.Steps Numerics.Profile.spec noHost
      (v1Config store frame addr mem (.store 1 0x11223344)).toLime.toCore target) :
    ∃ out, Runs original (.store 1 0x11223344) out ∧
      target = (v1Config store frame addr mem out).toLime.toCore ∧ target.frame = frame.toCore := by
  have ready : Admitted original (.store 1 0x11223344) := trivial
  rw [v1_to_lime, lime_to_core _ _ _ _ ready] at h
  obtain ⟨out, run, guard, eq⟩ := (core_run_iff (memory32_toCore limeFound) ready).mp h
  exact ⟨out, run, by rw [v1_to_lime, lime_to_core _ _ _ _ guard, eq],
    by rw [eq]; cases out <;> rfl⟩
