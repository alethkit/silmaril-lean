module

public meta import SqliteWasm.PreparedInvocation
public meta import Silmaril.Wasm.SingleThreaded.Exec.Interp

meta section

open SqliteWasm
open SqliteWasmArtifact (definedFunction?)
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded

private def linkedModule : ModuleInst :=
  { funcs := ((List.replicate 1517 0).set 23 1).set 1516 2
    globals := [0, 0]
    mems := [0] }

private def link (fn : Func) : Option (FuncInst Nat) := do
  let type ← (allocTypes sqlite.types)[fn.type.toNat]?
  return ⟨type, linkedModule, .wasm fn⟩

public def main : IO Unit := do
  let some version := definedFunction? sqlite 289
    | throw (IO.userError "version function missing from slot 289")
  let some funcs := [initializerFunction, initializerConstructor, threadSetupFunction, version].mapM link
    | throw (IO.userError "sequence replay function type missing")
  let mem : MemInst :=
    { type := ⟨.i32, ⟨0, none⟩⟩
      bytes := Memory.writeSlice ⟨Array.replicate 59984 0⟩ 59892 (Memory.encodeLE 4 17) }
  let initial : Store Nat :=
    { funcs, mems := [mem], globals := [⟨⟨.const, .i32⟩, .i32 0⟩] }
  let (first, firstDone) := Exec.runI neverFail 256 (invoke initial 0 [])
  let expected := threadSetupMemory (initializerMark mem 0) 17
  unless firstDone && first.code.isEmpty && decide (first.frame = {} ∧ first.store.mems = [expected]) do
    throw (IO.userError "initializer sequence replay disagreed with the expected memory or return")
  let (second, secondDone) := Exec.runI neverFail 8 (invoke first.store 3 [])
  unless secondDone && decide (second.frame = {} ∧ second.store.mems = first.store.mems ∧
      second.outcome? = some (.values [.i32 3054001])) do
    throw (IO.userError "version sequence replay disagreed with the expected memory or return")
  IO.println "Prepared initializer and version sequence replay passed"
