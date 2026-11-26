module

public import Silmaril.Machine.SeaOfNodes.Diamond.RTL.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Defs

/-! # Machine RTL for one source-native tail-tested word loop -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL

open Silmaril.Machine.Lir (Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Block Func Label Prog)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL
  (PortTy Reg WordOp emitOpsWith inputs model portIndex register registerWith word)
open Silmaril.SSA.SeaOfNodes.Loop (Graph Incoming headerPorts)
open Silmaril.SSA.RVSDG (Port)

abbrev headerSigs : List (List PortTy) :=
  [[.value word], [.value word], [.value .predicate]]

/-- Start latches the seed. Each activation computes the next word (wrapping
subtraction). When it is zero, Return reads the old carried word. Otherwise
the backedge latches the next word. -/
def graph : Graph WordOp inputs [word] [] headerSigs word where
  preheader := .nil
  header :=
    .cons .sub (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail .head)) .nil))
      (.cons (.const 0) .nil
        (.cons .ne (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))
          .nil))
  phiInputs
    | .entry => .cons (.arg .head) .nil
    | .backedge => .cons (.output (0 : Fin 3) .head) .nil
  predicate := .output (2 : Fin 3) .head
  result := .arg (.tail (.tail .head))

/-- The carried port is the loop parameter. Other ports retain the registers
bound at function entry. -/
def headerRegister {t : PortTy} (port : Port (headerPorts inputs [word]) t) : Reg :=
  match portIndex port with
  | 2 => .phi
  | i => .arg i

/-- Encode the source Phi operand in the actual predecessor's context. -/
def incomingRegister : Incoming → Reg
  | .entry => register ((graph.phiInputs .entry).get .head)
  | .backedge => registerWith headerRegister ((graph.phiInputs .backedge).get .head)

/-- Source block label and zero-based successor ordinal in the emitted
terminator. RTL lists the nonzero arm first. -/
def incomingSlot : Incoming → Label × Nat
  | .entry => (0, 0)
  | .backedge => (1, 0)

def preheader : Block Reg :=
  ⟨[.arg 0, .arg 1], [], .jump 1 [incomingRegister .entry]⟩

def header : Block Reg :=
  ⟨[.phi], emitOpsWith headerRegister graph.header,
    .cond (registerWith headerRegister graph.predicate)
      1 [incomingRegister .backedge] 2 [registerWith headerRegister graph.result]⟩

def exitBlock : Block Reg :=
  ⟨[.node 3], [], .ret [.node 3]⟩

def lowerFunc : Func Reg := ⟨⟨2, 1⟩, 0, [preheader, header, exitBlock]⟩

def lower : Prog Reg := ⟨[lowerFunc]⟩

/-- The expected numeric predicate encoding in the machine frame. -/
def nonzeroWord (next : Word) : Word :=
  Silmaril.Machine.Lir.ofBool (next != 0)

/-- Exact frame after executing the header producers. -/
def headerFrame (frame : Frame Reg) (old delta : Word) : Frame Reg :=
  ((frame.set (.node 0) (old - delta)).set (.node 1) 0).set (.node 2) (nonzeroWord (old - delta))

end Silmaril.Machine.SeaOfNodes.Loop.RTL
