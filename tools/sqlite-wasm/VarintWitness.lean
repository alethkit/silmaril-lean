module

public import SqliteWasm.ArtifactCheck
public import Silmaril.Formats.Sqlite.Varint.Defs
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Verify.Kernel.Thms

@[expose] public section

namespace SqliteWasm.VarintWitness

open Silmaril.Formats.Sqlite
open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Exec Silmaril.Wasm.Verify.Kernel
open SqliteWasmArtifact

set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-! Concrete executions of the quoted SQLite varint encoder and its callee. The fixture
uses a checked Core store with a one-page memory and the global used as a stack pointer. -/

def put : Func := (definedFunction? sqlite 530).get (by decide +kernel)
def putLong : Func := (definedFunction? sqlite 547).get (by decide +kernel)

def signature : DefType :=
  let group := (sqlite.types[12]?).get (by decide +kernel)
  ((allocTypes [group])[0]?).get (by decide +kernel)

def memoryType : MemoryType := ⟨.i32, ⟨1, none⟩⟩
def stackPointer : GlobalInst := ⟨⟨.var, Ty.i32⟩, .i32 128⟩
/-- The fixture preserves call index 547 through the function table. Unused slots also
point to store address 1, which has the required type for the call. -/
def moduleInst : ModuleInst :=
  { types := List.replicate 13 signature
    globals := [0]
    mems := [0]
    funcs := List.replicate 548 1 }

def entry (fn : Func) : FuncInst Unit := ⟨signature, moduleInst, .wasm fn⟩

def initialBytes : ByteArray :=
  ⟨⟨List.replicate 15 0 ++ [0x5a] ++ List.replicate 9 0 ++ [0xa5] ++
    List.replicate (Memory.pageSize - 26) 0⟩⟩

def initial : Store Unit :=
  { globals := [stackPointer], mems := [⟨memoryType, initialBytes⟩]
    funcs := [entry put, entry putLong] }

def threeByteValue : UInt64 := 16384
def nineByteValue : UInt64 := 0x01000000000000ad

def args (value : UInt64) : List Val := [.i32 16, .i64 value.toBitVec]

def expected (value : UInt64) (beforeOutput : ByteArray) : Config Unit :=
  let encoded := Varint.encode value
  let bytes := Memory.writeSlice beforeOutput 16 encoded.data
  ⟨initial.setMem 0 ⟨memoryType, bytes⟩, {}, [constI32 (BitVec.ofNat 32 encoded.length)]⟩

/-- For the three-byte path, the callee reverses its digits using scratch bytes at offsets
118 through 120. This specifies that side effect separately from the output at offset 16. -/
def threeByteScratch : ByteArray := Memory.writeSlice initialBytes 118 ⟨#[0, 128, 129]⟩

theorem fromOriginal :
    sourceFunction? original 530 = some put ∧ sourceFunction? original 547 = some putLong :=
  ⟨originalPutVarintFunction.trans (by kernel_rfl),
    originalPutVarintLongFunction.trans (by kernel_rfl)⟩

theorem helperSlot : moduleInst.funcs[547]? = some 1 := by kernel_rfl

private def typingContext : Context :=
  { types := moduleInst.types, funcs := List.replicate 548 signature
    globals := [stackPointer.type], mems := [memoryType] }

private theorem signatureOk : TyOk {} signature :=
  TyOk.check_sound (by decide +kernel)

private theorem aliasesTyped (n : Nat) :
    List.Forall₂ (fun address typ => ExternAddrOk initial (.func address) (.func typ))
      (List.replicate n 1) (List.replicate n signature) := by
  induction n with
  | zero => exact .nil
  | succ _ ih => exact .cons (.func (fi := entry putLong) rfl) ih

private theorem moduleTyped : ModuleInstOk initial moduleInst typingContext :=
  ModuleInstOk.mk (k := 0)
    (fun d membership =>
      (List.eq_of_mem_replicate (show d ∈ List.replicate 13 signature from membership)).symm ▸ signatureOk)
    .nil (.cons (.global (gi := stackPointer) rfl) .nil) (aliasesTyped 548)
    (.cons (.mem (mi := ⟨memoryType, initialBytes⟩) rfl) .nil) .nil
    (by simp [moduleInst]) .nil (by simp [moduleInst]) (by simp [moduleInst])
    (by simp [moduleInst]) (by simp [moduleInst])

private theorem putTyped : FuncOk typingContext put signature :=
  defaultCheckers_sound.func (by kernel_rfl)

private theorem putLongTyped : FuncOk typingContext putLong signature :=
  defaultCheckers_sound.func (by kernel_rfl)

private theorem memoryLength : initialBytes.size = Memory.pageSize := by kernel_rfl

private theorem memoryTyped : MemInstOk ⟨memoryType, initialBytes⟩ :=
  ⟨memCheck_sound (by decide +kernel), memoryLength.trans (Nat.one_mul _).symm⟩

theorem initialTyped : StoreOk initial where
  tags := by simp [initial]
  globals := by
    intro global membership
    simp only [initial, List.mem_singleton] at membership
    subst global
    exact ⟨TyOk.check_sound (by decide +kernel), .num _⟩
  mems := by simpa [initial] using memoryTyped
  tables := by simp [initial]
  funcs := by
    intro fi membership
    simp only [initial, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · exact .wasm signatureOk moduleTyped rfl putTyped (Sub.refl _ (k := .def) trivial signature)
    · exact .wasm signatureOk moduleTyped rfl putLongTyped (Sub.refl _ (k := .def) trivial signature)
  elems := by simp [initial]
  structs := by simp [initial]
  arrays := by simp [initial]
  exns := by simp [initial]
  acyclicStructs := by simp [initial]
  acyclicArrays := by simp [initial]
  acyclicExns := by simp [initial]
  structsClosed := by simp [initial]
  arraysClosed := by simp [initial]

theorem runThree :
    runInvokeK neverFail 300 initial 0 (args threeByteValue) =
      some (expected threeByteValue threeByteScratch, true, some (.values [.i32 3])) := by
  kernel_rfl

theorem runNine :
    runInvokeK neverFail 300 initial 0 (args nineByteValue) =
      some (expected nineByteValue initialBytes, true, some (.values [.i32 9])) := by
  kernel_rfl

private theorem invocationTyped (value : UInt64) : InvokeOk initial 0 (args value) :=
  ⟨entry put, .cons Ty.i32 (.cons Ty.i64 .nil), .cons Ty.i32 .nil, rfl,
    Expand.iff.mpr rfl, .cons (.num _) (.cons (.num _) .nil)⟩

private theorem execution {value : UInt64} {final : Config Unit} {result : Result}
    (ran : runInvokeK neverFail 300 initial 0 (args value) = some (final, true, some result)) :
    Steps (profile neverFail) Det.noHost (invoke initial 0 (args value)) final := by
  rw [runInvokeK_eq] at ran
  exact InvokeRun.runInvoke?_steps_noHost initialTyped (invocationTyped value) ran

/-- The invocation writes the three-byte Lean encoding and changes the specified scratch bytes. -/
theorem reachesThree :
    Steps (profile neverFail) Det.noHost (invoke initial 0 (args threeByteValue))
      (expected threeByteValue threeByteScratch) :=
  execution runThree

/-- The invocation writes the nine-byte Lean encoding and preserves memory outside the output. -/
theorem reachesNine :
    Steps (profile neverFail) Det.noHost (invoke initial 0 (args nineByteValue))
      (expected nineByteValue initialBytes) :=
  execution runNine

#print axioms fromOriginal
#print axioms helperSlot
#print axioms initialTyped
#print axioms runThree
#print axioms runNine
#print axioms reachesThree
#print axioms reachesNine

end SqliteWasm.VarintWitness
