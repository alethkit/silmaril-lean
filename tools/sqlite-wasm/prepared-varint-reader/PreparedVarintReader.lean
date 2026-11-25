module

public import SqliteWasm.DirectPreparation
public import SqliteWasm.GetVarint
import Silmaril.Wasm.Link.Preparation
import Silmaril.Wasm.Verify.Kernel.Defs

public section

namespace SqliteWasm

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (DefType Expand Ty)
open SqliteWasmArtifact

set_option maxRecDepth 65536

private def readerFunction : Func := (definedFunction? sqlite 434).get (by kernel_rfl)

private def readerType : DefType := ((allocTypes sqlite.types)[readerFunction.type.toNat]?).get (by kernel_rfl)

/-- The directly prepared reactor supplies the reader's runtime bindings.
A successful read and destination bounds give the exact Core call effect. -/
theorem reactorPreparedReader (P : Profile) (host : HostSemantics Nat) :
    ∃ runtime frame mem memoryAddress,
      prepareDirect? evalConst? reactorTypedImports sqlite reactorImportAddrs =
        some (runtime, frame, none) ∧
      runtime.mem? frame ⟨0⟩ = some (memoryAddress, mem) ∧
      ∀ {src dst : BitVec 32} {value : UInt64} {next : Nat},
        Varint.read? (File.View.ofBytes ⟨mem.bytes⟩) src.toNat = some (value, next) →
        dst.toNat + 8 ≤ mem.bytes.size →
        Steps P host ⟨runtime, frame, vals [.i32 src, .i32 dst] ++ [.plain (.call ⟨434⟩)]⟩
          ⟨runtime.setMem memoryAddress
            { mem with bytes := Memory.writeSlice mem.bytes dst.toNat (Memory.encodeLE 8 value.toNat) },
            frame, [constI32 (BitVec.ofNat 32 (next - src.toNat))]⟩ := by
  obtain ⟨before, allocated, runtime, frame, mem, prepared, alloc, sameFunctions, _, _, mapped, _, _, _⟩ :=
    reactorDirectPreparation
  have bindings := Link.GC.Preparation.allocModule_function
    (as := List.range 23) (n := 411) (fn := readerFunction) (d := readerType) alloc
    (by kernel_rfl) (by kernel_rfl)
  have selected : definedFunction? sqlite 434 = some readerFunction := by kernel_rfl
  have slot : frame.module.funcs[434]? = some (before.funcs.length + 411) := by
    simpa only [List.length_range] using bindings.1
  have entry :
      runtime.funcs[before.funcs.length + 411]? = some ⟨readerType, frame.module, .wasm readerFunction⟩ := by
    rw [sameFunctions]
    exact bindings.2
  have signature : Expand readerType (.func (.cons Ty.i32 (.cons Ty.i32 .nil)) (.cons Ty.i32 .nil)) :=
    Expand.iff.mpr (by kernel_rfl)
  refine ⟨runtime, frame, mem, before.mems.length, prepared, mapped, ?_⟩
  intro src dst value next read bounds
  exact getVarint_of_read selected slot entry rfl signature mapped read bounds

#print axioms reactorPreparedReader

end SqliteWasm
