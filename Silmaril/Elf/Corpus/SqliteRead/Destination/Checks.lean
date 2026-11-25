module

import Silmaril.Elf.Corpus.SqliteRead.Destination.Thms
import Silmaril.X86.EntryState
meta import Silmaril.Elf.Corpus.SqliteRead.Defs
meta import Silmaril.X86.EntryState

namespace Silmaril.Elf.Corpus.SqliteRead.Destination

open Silmaril.Elf.Corpus.SqliteRead
open Silmaril.X86 (MState Word)
open Silmaril.X86.EntryState
open Silmaril.X86.Ext.Wire (Platform)
open Silmaril.Machine.LittleEndian (encodeWords)

private def page : PageRead := ⟨0x500000, 0x600000, 3, 2⟩
private def methods : Word := 0x10e220
private def target : Word := 0x159b0
private def platform : Platform := ⟨fun _ _ => ⟨0, 0, 0, 0⟩⟩
private def payload : List (BitVec 8) := [0xa1, 0xb2, 0xc3]

private def placements (readable writable : Bool) : List Placement :=
  [⟨⟨region.base, region.bytes.length, ⟨true, false, true⟩⟩, some region.bytes⟩,
    ⟨⟨page.file.toNat, 8, ⟨true, false, false⟩⟩, some (encodeWords [methods])⟩,
    ⟨⟨(methods + 16).toNat, 8, ⟨true, false, false⟩⟩, some (encodeWords [target])⟩,
    ⟨⟨0x6ffff8, 8, ⟨true, true, false⟩⟩, none⟩,
    ⟨⟨page.buffer.toNat, 3, ⟨readable, writable, false⟩⟩, some payload⟩]

private def fixture (readable writable : Bool) : MState :=
  ⟨⟨(fun reg => match reg with
      | .rdi => page.file
      | .rsi => page.buffer
      | .rdx => 3
      | .rcx => 2
      | .rsp => 0x700000
      | _ => 0), 0x4b10d, unknownFlags, 0⟩, memory (placements readable writable)⟩

private def boundary (initial : MState) :
    Option (Nat × Option (List (BitVec 8)) × Bool × Option (List (BitVec 8)) × Bool) :=
  match run platform 3 initial with
  | .handlerEntry reached =>
    let request := argument reached.core
    let base := request.buffer.toNat
    let length := request.amount.toNat
    some (request.offset.toNat, initial.memory.readBytes base length,
      initial.memory.checkSpan .write base length, reached.memory.readBytes base length,
      reached.memory.checkSpan .write base length)
  | _ => none

#guard boundary (fixture true true) == some (6, some payload, true, some payload, true)
#guard boundary (fixture false false) == some (6, none, false, none, false)
#guard boundary (fixture false true) == some (6, none, true, none, true)

#print axioms dispatch_destination_observation

end Silmaril.Elf.Corpus.SqliteRead.Destination
