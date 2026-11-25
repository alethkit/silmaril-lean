module

public import SqliteWasm.PreparedInvocation

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

set_option maxRecDepth 65536

private theorem updatedMemory {s : Store Nat} {frame : Frame} {address : Nat}
    {mem : MemInst} (found : s.mem? frame ⟨0⟩ = some (address, mem)) (after : MemInst) :
    (s.setMem address after).mem? frame ⟨0⟩ = some (address, after) := by
  change (frame.module.mems[0]?.bind fun a => s.mems[a]?.bind fun m => some (a, m)) = _ at found
  obtain ⟨a, slot, lookup⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨m, entry, same⟩ := Option.bind_eq_some_iff.mp lookup
  obtain ⟨sameAddress, sameMemory⟩ := Prod.mk.inj (Option.some.inj same)
  subst a
  subst m
  change (frame.module.mems[0]?.bind fun a =>
    (s.mems.set address after)[a]?.bind fun m => some (a, m)) = _
  rw [slot, Option.bind_some, List.getElem?_set_self (List.getElem?_eq_some_iff.mp entry).1]
  rfl

/-- A second invocation of the named initializer traps on the marker installed by
the first call, in its exact output store. -/
theorem reactorPreparedInitReentry (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem memoryAddress fi,
      let after := threadSetupMemory (initializerMark mem 0) 0
      let initialized := runtime.setMem memoryAddress after
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      frame.module.exports.find? (·.name == "_initialize") = some ⟨"_initialize", .func 25⟩ ∧
      frame.module.funcs[25]? = some 25 ∧
      runtime.funcs[25]? = some fi ∧
      initialized.funcs[25]? = some fi ∧
      fi.module = frame.module ∧
      fi.code = .wasm initializerFunction ∧
      initialized.mem? (Frame.forCall fi.module [] initializerFunction.locals) ⟨0⟩ =
        some (memoryAddress, after) ∧
      Memory.load after.bytes (initializerAddress 0) 4 = some 1 ∧
      InvokeOk runtime 25 [] ∧
      Steps P host (invoke runtime 25 []) ⟨initialized, {}, []⟩ ∧
      InvokeOk initialized 25 [] ∧
      Steps P host (invoke initialized 25 []) ⟨initialized, {}, [.trap]⟩ := by
  obtain ⟨runtime, frame, mem, memoryAddress, prepared, exported, mapped, initOk, runInit⟩ :=
    reactorPreparedInvocation P host
  obtain ⟨before, allocated, directStore, directFrame, directMem, prepared', alloc, sameFunctions,
    initSlot, base, mapped', size, _, _⟩ := reactorDirectPreparation
  obtain ⟨sameStore, frameAndStart⟩ := Prod.mk.inj (Option.some.inj (prepared.symm.trans prepared'))
  have sameFrame := (Prod.mk.inj frameAndStart).1
  subst directStore
  subst directFrame
  have sameMem := (Prod.mk.inj (Option.some.inj (mapped.symm.trans mapped'))).2
  subst directMem
  obtain ⟨address, fi, _, slot, allocatedEntry, moduleEq, code, signature⟩ :=
    allocatedInitializeExport alloc (by rfl)
  have sameAddress := Option.some.inj (slot.symm.trans initSlot)
  subst address
  let after := threadSetupMemory (initializerMark mem 0) 0
  let initialized := runtime.setMem memoryAddress after
  have entry : runtime.funcs[25]? = some fi := sameFunctions.symm ▸ allocatedEntry
  have retained : initialized.funcs[25]? = some fi := entry
  have postMapped :
      initialized.mem? (Frame.forCall fi.module [] initializerFunction.locals) ⟨0⟩ =
        some (memoryAddress, after) := by
    rw [moduleEq]
    exact updatedMemory mapped after
  have postBase :
      initialized.global? (Frame.forCall fi.module [] initializerFunction.locals) ⟨1⟩ =
        some (before.globals.length + 1, ⟨⟨.const, .i32⟩, .i32 0⟩) := by
    rw [moduleEq]
    exact base
  have marked : Memory.load after.bytes (initializerAddress 0) 4 = some 1 :=
    initializerFlagStaysMarked mem 0 (by omega)
  have trap := (initializerTrapsOnNonzero (P := P) (host := host) (caller := frame)
    initSlot retained code signature postMapped postBase marked (by decide)).2
  exact ⟨runtime, frame, mem, memoryAddress, fi, prepared, exported, initSlot, entry, retained,
    moduleEq, code, postMapped, marked, initOk, runInit,
    ⟨fi, .nil, .nil, retained, signature, .nil⟩, trap⟩

#print axioms reactorPreparedInitReentry

end SqliteWasm
