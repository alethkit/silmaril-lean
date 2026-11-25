module

public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.SingleThreaded.Exec.InterpTyped
public import Silmaril.Crypto.SHA256.Kernel

/-! The exact freestanding Clang fixture for the new working word a of one
SHA-256 round. The source and rebuild commands live in tests/crypto/sha256-wasm. -/
@[expose] public section
namespace Silmaril.Wasm.Examples.Sha256Round

open Silmaril.Crypto.SHA256.Kernel (Word)
open Execution.Core

/-- The linked wasm32 module. See the project guide for compiler and byte identities. -/
def fixture : ByteArray := ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x0e, 0x01, 0x60,
  0x09, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x01, 0x7f,
  0x03, 0x02, 0x01, 0x00, 0x05, 0x03, 0x01, 0x00, 0x02, 0x06, 0x08, 0x01,
  0x7f, 0x01, 0x41, 0x80, 0x88, 0x04, 0x0b, 0x07, 0x1b, 0x02, 0x06, 0x6d,
  0x65, 0x6d, 0x6f, 0x72, 0x79, 0x02, 0x00, 0x0e, 0x73, 0x68, 0x61, 0x32,
  0x35, 0x36, 0x5f, 0x72, 0x6f, 0x75, 0x6e, 0x64, 0x5f, 0x61, 0x00, 0x00,
  0x0a, 0x4b, 0x01, 0x49, 0x00, 0x20, 0x01, 0x20, 0x00, 0x72, 0x20, 0x02,
  0x71, 0x20, 0x01, 0x20, 0x00, 0x71, 0x72, 0x20, 0x00, 0x41, 0x1e, 0x77,
  0x20, 0x00, 0x41, 0x13, 0x77, 0x73, 0x20, 0x00, 0x41, 0x0a, 0x77, 0x73,
  0x6a, 0x20, 0x06, 0x6a, 0x20, 0x03, 0x41, 0x1a, 0x77, 0x20, 0x03, 0x41,
  0x15, 0x77, 0x73, 0x20, 0x03, 0x41, 0x07, 0x77, 0x73, 0x6a, 0x20, 0x07,
  0x6a, 0x20, 0x05, 0x20, 0x04, 0x73, 0x20, 0x03, 0x71, 0x20, 0x05, 0x73,
  0x6a, 0x20, 0x08, 0x6a, 0x0b
]⟩

/-- Select the type and definition of the named export in an import-free module.
Rejecting imports keeps the function index in the defined-function index space. -/
def exportedRound? (bytes : ByteArray) : Option (RecType × Func) := do
  let decoded ← (Binary.Core.Decode.decodeModule bytes).toOption
  if !decoded.imports.isEmpty then none else
    let exported ← decoded.exports.find? fun e => e.name == "sha256_round_a"
    let .func index := exported.index | none
    let fn ← decoded.funcs[index.toNat]?
    return (← decoded.types[fn.type.toNat]?, fn)

def signature : RecType :=
  ⟨[⟨true, [], .func ⟨List.replicate 9 .i32, [.i32]⟩⟩]⟩

/-- The instruction list checked against the function selected by the decoder. -/
def body : Expr :=
  let get (i : Fin (2 ^ 32)) := Instr.localGet ⟨i⟩
  let push := Instr.intConst .i32
  let bin := Instr.intBinOp .i32
  [get 1, get 0, bin .or, get 2, bin .and, get 1, get 0, bin .and, bin .or,
   get 0, push 30, bin .rotl, get 0, push 19, bin .rotl, bin .xor,
   get 0, push 10, bin .rotl, bin .xor, bin .add, get 6, bin .add,
   get 3, push 26, bin .rotl, get 3, push 21, bin .rotl, bin .xor,
   get 3, push 7, bin .rotl, bin .xor, bin .add, get 7, bin .add,
   get 5, get 4, bin .xor, get 3, bin .and, get 5, bin .xor, bin .add,
   get 8, bin .add]

structure Input where
  a : Word
  b : Word
  c : Word
  e : Word
  f : Word
  g : Word
  h : Word
  k : Word
  w : Word

def Input.frame (input : Input) (instance_ : ModuleInst) : Frame :=
  { module := instance_
    locals := [input.a, input.b, input.c, input.e, input.f, input.g, input.h, input.k, input.w]
      |>.map fun bits => some (.i32 bits) }

/-- Enter the decoded body with its nine i32 parameters already initialized. -/
def entry {H : Type} (input : Input) (store : Store H) (instance_ : ModuleInst) : Config H :=
  ⟨store, input.frame instance_, body.map Admin.plain⟩

def fuel : Nat := body.length + 1

end Silmaril.Wasm.Examples.Sha256Round
