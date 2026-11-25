module

public import Silmaril.X86.Open.Defs
public import Silmaril.X86.FnContract.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Defs

/-! A forward graph for the public GCC SQLite `sqlite3_str_length` slice.
The graph retains the null decision, one guarded read, and the common RET. -/

@[expose] public section
namespace Silmaril.Machine.Region.X86.SqliteStrLength

open Silmaril.X86
open Silmaril.Process (Memory addressLimit)
open Silmaril.SSA.LambdaRTL
open Silmaril.Machine.Execution (run)

/-- SQLite 3.54.1 default GCC x86-64 ELF at VA/file offset 0x10060. -/
def code : List Byte := [0x31, 0xc0, 0x48, 0x85, 0xff, 0x74, 0x03, 0x8b, 0x47, 0x18, 0xc3]

inductive Register where
  | pointer | result | payload
  deriving DecidableEq

/-- Internal load block and outward transfer to the common RET. -/
inductive Label where
  | load | ret
  deriving DecidableEq

inductive Operation where
  | loadLength

def pointer (entry : MState) : Word := entry.core.read .rdi

def zeroExtendLength (value : Word) : Word := (value.setWidth 32).setWidth 64

def field (memory : Memory) (ptr : Word) : Option Word :=
  Ext.loadN memory (ptr + 0x18) 4

/-- The only instruction in this graph is the actual four-byte memory read.
The case splits the pointer into non-null and null arms. -/
def model (memory : Memory) : Model Operation Option Word where
  unit := 0
  pair a _ := a
  inl := id
  inr := id
  unpair _ := none
  split ptr := some (if ptr = 0 then .inr 0 else .inl 0)
  app _ ptr := (field memory ptr).map zeroExtendLength
  abort _ := none

def entryStore (entry : MState) : Register → Word
  | .pointer => pointer entry
  | .result => entry.core.read .rax
  | .payload => 0

/-- `ret` is the CFG's outward label for reaching the common `ret` opcode. -/
def graph : CFG Register Label Operation :=
  ⟨.let1 .result (.val .unit)
      (.term (.case (.val (.var .pointer)) .payload (.br .load (.var .pointer))
        .payload (.br .ret (.var .result)))),
    [(.load, ⟨.pointer, .let1 .result (.app .loadLength (.var .pointer)) (.term (.br .ret (.var .result)))⟩)]⟩

def branchOffset : Label → Word
  | .load => 7
  | .ret => 10

def nextLabel (entry : MState) : Label := if pointer entry = 0 then .ret else .load

/-- The non-null arm requires a successful four-byte read at the modeled
effective address. The null arm imposes no condition on data memory. -/
def DataReady (entry : MState) : Prop :=
  pointer entry ≠ 0 → ∃ value, field entry.memory (pointer entry) = some value

/-- The x86 return instruction only needs this readable saved address. -/
def ReturnSlot (entry : MState) : Prop :=
  entry.memory.readBytes (entry.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [FnContract.retOf entry.core entry.memory])

/-- Successful open x86 first return through the same branch and outward
result as the forward CFG. The CFG exits at the common `ret` instruction. -/
def Bridge (entry final : MState) : Prop :=
  ∃ target branch preRet,
    graph.entry.exec (model entry.memory) (fun label _ _ => some label) (entryStore entry) = some target ∧
    run Open.step 3 entry = some branch ∧
    branch.core.rip = entry.core.rip + branchOffset target ∧
    ((target = .ret ∧ preRet = branch) ∨ (target = .load ∧ Open.step branch = some preRet)) ∧
    preRet.core.rip = entry.core.rip + 10 ∧ Open.step preRet = some final ∧
    (obs <$> graph.run (model entry.memory) (entryStore entry)) = some (.ret, final.core.read .rax) ∧
    final.memory = entry.memory

end Silmaril.Machine.Region.X86.SqliteStrLength
