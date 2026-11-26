module

public import Silmaril.Machine.RTL.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Defs
public import Silmaril.SSA.RVSDG.Isomorphism.Defs

/-! # Machine RTL for the native counted-swap bank

The two payload words share a block-argument transfer with a separate loop
index. The target reads the two crossed operands before writing either
destination. Both source and target use 64-bit words.
-/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank

open Silmaril.Machine.Lir (Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Block Func Label Op Prog)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Model ValueSort dataPorts)
open Silmaril.SSA.SeaOfNodes.Loop (Graph Incoming)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA (Inputs word wordPort)
open Silmaril.SSA.RVSDG (Address Wires)

abbrev PortTy := Silmaril.SSA.SeaOfNodes.Diamond.Ty Unit

abbrev SwapOp := Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Op
abbrev NativeGraph := Graph SwapOp [word, word, word] [word, word, word]
  [[wordPort]] [[.value .predicate], [wordPort], [wordPort]] word

abbrev graph : NativeGraph := Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.graph

/-- Unsigned index test, unit increment, and a return that observes both
payload words in order. The source primitives are evaluated on native words. -/
def model : Model SwapOp where
  value _ := Word
  run
    | .seed, .nil => (0 : Word)
    | .test, .cons index (.cons limit .nil) =>
        ⟨decide ((index : Word).toNat < (limit : Word).toNat)⟩
    | .advance, .cons index .nil => BitVec.add index (1 : Word)
    | .observe, .cons first (.cons second .nil) => BitVec.sub first second

abbrev input := Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.input model
abbrev bank (first second index : Word) :=
  Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.carried model first second index

inductive Reg where
  | arg (index : Nat)
  | pre (index : Nat)
  | node (index : Nat)
  | first
  | second
  | index
  | one
  | result
  deriving DecidableEq, Repr

def entryAddress : Address → Reg
  | .arg i => .arg i
  | .output i _ => .pre i

def headerAddress : Address → Reg
  | .arg 3 => .first
  | .arg 4 => .second
  | .arg 5 => .index
  | .arg i => .arg i
  | .output i _ => .node i

def emitOp {args : List PortTy}
    {past : List (List PortTy)}
    {ins : List (ValueSort Unit)} {out : ValueSort Unit}
    (resolve : Address → Reg) (dest : Reg) : SwapOp ins out → Wires args past (dataPorts ins) → Op Reg
  | .seed, _ => .const dest 0
  | .test, w =>
      .binary (.cmp .ltu) dest (resolve (w.get .head).address) (resolve (w.get (.tail .head)).address)
  | .advance, w => .binary .add dest (resolve (w.get .head).address) .one
  | .observe, w =>
      .binary .sub dest (resolve (w.get .head).address) (resolve (w.get (.tail .head)).address)

def emitOps {args : List PortTy}
    (resolve : Address → Reg) (dest : Nat → Reg) :
    {past sigs : List (List PortTy)} →
      Dataflow SwapOp args past sigs → List (Op Reg)
  | _, _, .nil => []
  | past, _, .cons op operands rest =>
      emitOp resolve (dest past.length) op operands :: emitOps resolve dest rest

def incomingRegisters : Incoming → List Reg
  | .entry => (graph.phiInputs .entry).addresses.map entryAddress
  | .backedge => (graph.phiInputs .backedge).addresses.map headerAddress

/-- The source block label and zero-based successor ordinal in that block. -/
def incomingSlot : Incoming → Label × Nat
  | .entry => (0, 0)
  | .backedge => (1, 0)

def preheader : Block Reg :=
  ⟨[.arg 0, .arg 1, .arg 2], emitOps entryAddress .pre graph.preheader ++ [.const .one 1],
    .jump 1 (incomingRegisters .entry)⟩

def header : Block Reg :=
  ⟨[.first, .second, .index], emitOps headerAddress .node graph.header,
    .cond (headerAddress graph.predicate.address)
      1 (incomingRegisters .backedge) 2 [headerAddress graph.result.address]⟩

def exitBlock : Block Reg := ⟨[.result], [], .ret [.result]⟩

def lowerFunc : Func Reg := ⟨⟨3, 1⟩, 0, [preheader, header, exitBlock]⟩

def lower : Prog Reg := ⟨[lowerFunc]⟩

/-- A code for each typed source producer. Its inputs and result sorts are
determined by the constructor. -/
inductive Opcode where
  | seed
  | test
  | advance
  | observe
  deriving DecidableEq

def opcode {ins : List (ValueSort Unit)} {out : ValueSort Unit} : SwapOp ins out → Opcode
  | .seed => .seed
  | .test => .test
  | .advance => .advance
  | .observe => .observe

def tableCode {args : List PortTy}
    {past sigs : List (List PortTy)} :
    Dataflow SwapOp args past sigs → List (Opcode × List Address)
  | .nil => []
  | .cons op operands rest => (opcode op, operands.addresses) :: tableCode rest

structure GraphCode where
  preheader : List (Opcode × List Address)
  header : List (Opcode × List Address)
  entry : List Address
  feedback : List Address
  predicate : Address
  result : Address
  deriving DecidableEq

def graphCode (g : NativeGraph) : GraphCode :=
  ⟨tableCode g.preheader, tableCode g.header, (g.phiInputs .entry).addresses,
    (g.phiInputs .backedge).addresses, g.predicate.address, g.result.address⟩

/-- Check opcodes and exact addresses in their typed predecessor scopes. -/
def lowerChecked (g : NativeGraph) : Option (Prog Reg) :=
  if graphCode g = graphCode graph then some lower else none

/-- Write the two payload words and the index from an already read tuple. -/
def bindBank (fr : Frame Reg) (first second index : Word) : Frame Reg :=
  ((fr.set .first first).set .second second).set .index index

def wordArgs (args : Inputs Word) : List Word := [args.limit, args.first, args.second]

end Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank
