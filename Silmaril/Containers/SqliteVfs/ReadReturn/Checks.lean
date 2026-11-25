module

import Silmaril.Containers.SqliteVfs.ReadReturn.Thms
import Init.Omega

namespace Silmaril.Containers.SqliteVfs.ReadReturn

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.ReadEntry (projectEntry)
open Silmaril.Machine
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary
open Silmaril.Machine.SqliteRead (BufferView Status)

private def request : SqliteRead.Request := ⟨1, 32, 2, 0⟩
private def page : Page := ⟨⟨0⟩, 1, 2⟩
private def binding : FileBinding := fun pointer => if pointer = 1 then some ⟨0⟩ else none
private theorem bound : binding request.file = some page.handle := rfl

private def env : SqliteRead.Context := ⟨fun _ => True, fun _ _ => True⟩
private def cache : Cache := fun slot => if slot = 0 then some .vacant else none
private def initial : BufferView := fun _ => none
private def written (last : BitVec 8) : BufferView :=
  fun address => if address = 32 then some 10 else if address = 33 then some last else none

private theorem admitted : env.Admits request :=
  ⟨by decide, trivial, by decide, by decide, by decide, by decide, by decide, trivial⟩

private theorem frame (last : BitVec 8) : SqliteRead.Framed request initial (written last) := by
  intro address outside
  change address < 32 ∨ 34 ≤ address at outside
  simp [written, initial, show address ≠ 32 from by omega, show address ≠ 33 from by omega]

private theorem writes (last : BitVec 8) : SqliteRead.Writes request (written last) [10, last] := by
  intro i within
  change i < 2 at within
  have index : i = 0 ∨ i = 1 := by omega
  rcases index with rfl | rfl <;> rfl

private theorem copied (last : BitVec 8) :
    bufferBytes? request (written last) = some [10, UInt8.ofBitVec last] := by
  change List.ofFnM (fun i : Fin 2 =>
    (written last (32 + i.val)).map UInt8.ofBitVec) = _
  simp only [List.ofFnM_succ_last, List.ofFnM_zero]
  rfl

private def full : FileState := ⟨[10, 20], some .readOnly, 0⟩
private def short : FileState := ⟨[10], some .readOnly, 0⟩

private theorem blocked_of_return {file : FileState} {last : BitVec 8} {status : Status}
    {exchange : Exchange} (live : (file.mode page.handle).isNone = false)
    (law : SqliteRead.Handler (file.bytes.map UInt8.toBitVec) request initial (written last) status)
    (supported : status = .ok ∨ status = .shortRead)
    (returns : projectReturn binding request (written last) status = some exchange) :
    (runtime (readOnly 8)).beh file (.blocked (encode [exchange])) := by
  obtain ⟨actual, projected, _, _, _, blocked⟩ :=
    returning_handler_completes (binding := binding) request page env file 8 cache 0 initial (written last)
      status admitted ⟨rfl, rfl, rfl⟩ (by decide) live rfl law supported
  exact (Option.some.inj (projected.symm.trans returns)) ▸ blocked

example : (runtime (readOnly 8)).beh full
    (.blocked (encode [⟨page.request, .ok [10, 20]⟩])) :=
  blocked_of_return (status := .ok) rfl ⟨frame 20, rfl, writes 20⟩ (.inl rfl) (by
    simp [projectReturn, copied, bound]
    rfl)

example : (runtime (readOnly 8)).beh short
    (.blocked (encode [⟨page.request, .shortRead [10, 0]⟩])) :=
  blocked_of_return (status := .shortRead) rfl ⟨frame 0, by decide, writes 0⟩ (.inr rfl) (by
    simp [projectReturn, copied, bound]
    rfl)

example : projectReturn binding request (written 20) (.other 1) = none := rfl

private def missing : BufferView := fun address => if address = 32 then some 10 else none

example : projectReturn binding request missing .shortRead = none := by
  have absent : bufferBytes? request missing = none := by
    change List.ofFnM (fun i : Fin 2 => (missing (32 + i.val)).map UInt8.ofBitVec) = none
    simp only [List.ofFnM_succ_last, List.ofFnM_zero]
    rfl
  simp [projectReturn, absent, bound]

example : projectReturn binding { request with file := 2 } (written 20) .ok = none := rfl

#print axioms returning_handler_completes

end Silmaril.Containers.SqliteVfs.ReadReturn
