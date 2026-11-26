module

public import Silmaril.Machine.SeaOfNodes.Diamond.RTL.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Defs
public import Silmaril.SSA.RVSDG.Isomorphism.Defs

/-! # Typed word columns and a routed three-payload RTL loop -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing

open Silmaril.Machine.Lir (Word ofBool)
open Silmaril.Machine.RTL.SSA (Block Func Prog)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp emitOpsWith model word)
open Silmaril.SSA.RVSDG (Address Origin Port Tuple Wires extend)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Val dataPorts)
open Silmaril.SSA.SeaOfNodes.Loop (Graph Incoming appendTuple)

abbrev wordPort : PortTy := .value word
abbrev wordPorts (n : Nat) : List PortTy := List.replicate n wordPort
abbrev WordTuple (n : Nat) := Tuple (Val model.value) (wordPorts n)
abbrev ArgumentColumn (scope arity : Nat) := Wires (wordPorts scope) [] (wordPorts arity)

/-- Header operand registers preserve the native argument positions. The
producer register namespace is separate from both banks of arguments. -/
def register : Address → Reg
  | .arg i => .arg i
  | .output i _ => .node i

/-- Emit the complete ordered operand column for a single transfer. -/
def emitColumn {args : List PortTy} {past : List (List PortTy)} {arity : Nat}
    (wires : Wires args past (wordPorts arity)) : List Reg :=
  wires.addresses.map register

def words : {n : Nat} → WordTuple n → List Word
  | 0, .nil => []
  | _ + 1, .cons head tail => head :: words tail

def argumentPort : (n : Nat) → Fin n → Port (wordPorts n) wordPort
  | 0, i => i.elim0
  | n + 1, i => Fin.cases .head (fun j => .tail (argumentPort n j)) i

/-- Check the arity and each source argument index before building typed
wires. Duplicate operand indices are valid. -/
def checkColumn (scope : Nat) : (arity : Nat) → List Nat → Option (ArgumentColumn scope arity)
  | 0, [] => some .nil
  | arity + 1, i :: rest =>
    if h : i < scope then
      (checkColumn scope arity rest).map (.cons (.arg (argumentPort scope ⟨i, h⟩)))
    else none
  | _, _ => none

/-- Extend the producer scope of an argument-only column. -/
def extendArguments {args users : List PortTy} (past : List (List PortTy))
    (wires : Wires args [] users) : Wires args past users :=
  wires.map fun _ wire => match wire with
    | .arg p => .arg p
    | .output i _ => i.elim0

abbrev inputSorts := [word, word, word, word]
abbrev carriedSorts := [word, word, word, word]
abbrev headerSigs : List (List PortTy) := [[wordPort], [wordPort], [wordPort], [.value .predicate]]

/-- Three payload slots can read any argument visible at their predecessor.
The first argument and the first carried slot are reserved for loop control. -/
structure Routes where
  entry : ArgumentColumn 4 3
  feedback : ArgumentColumn 8 3

def checkRoutes (entry feedback : List Nat) : Option Routes :=
  (checkColumn 4 3 entry).bind fun initial =>
    (checkColumn 8 3 feedback).map fun next => ⟨initial, next⟩

def Routes.graph (routes : Routes) : Graph WordOp inputSorts carriedSorts [] headerSigs word where
  preheader := .nil
  header :=
    let counterPort := argumentPort 8 ⟨4, by decide⟩
    .cons (.const 1) .nil
      (.cons .sub (.cons (.arg counterPort) (.cons (.output (0 : Fin 1) .head) .nil))
        (.cons (.const 0) .nil
          (.cons .ne (.cons (.arg counterPort) (.cons (.output (2 : Fin 3) .head) .nil)) .nil)))
  phiInputs
    | .entry => .cons (.arg .head) routes.entry
    | .backedge => .cons (.output (1 : Fin 4) .head) (extendArguments (extend [] headerSigs) routes.feedback)
  predicate := .output (3 : Fin 4) .head
  result := .arg (argumentPort 8 ⟨5, by decide⟩)

def Routes.incomingRegisters (routes : Routes) : Incoming → List Reg
  | .entry => emitColumn (arity := 4) (routes.graph.phiInputs .entry)
  | .backedge => emitColumn (arity := 4) (routes.graph.phiInputs .backedge)

def entryParams : List Reg := [.arg 0, .arg 1, .arg 2, .arg 3]
def bankParams : List Reg := [.arg 4, .arg 5, .arg 6, .arg 7]

def Routes.preheader (routes : Routes) : Block Reg :=
  ⟨entryParams, [], .jump 1 (routes.incomingRegisters .entry)⟩

def Routes.header (routes : Routes) : Block Reg :=
  ⟨bankParams, emitOpsWith (fun p => .arg p.index) routes.graph.header,
    .cond (register routes.graph.predicate.address) 1 (routes.incomingRegisters .backedge)
      2 [register routes.graph.result.address]⟩

def exitBlock : Block Reg := ⟨[.phi], [], .ret [.phi]⟩

def Routes.lowerFunc (routes : Routes) : Func Reg :=
  ⟨⟨4, 1⟩, 0, [routes.preheader, routes.header, exitBlock]⟩

def Routes.lower (routes : Routes) : Prog Reg := ⟨[routes.lowerFunc]⟩

/-- Decode the typed columns and run the machine's SSA check on the emitted CFG. -/
def lowerChecked (entry feedback : List Nat) : Option (Prog Reg) :=
  (checkRoutes entry feedback).bind fun routes =>
    if routes.lowerFunc.WellFormed then some routes.lower else none

/-- Convenient constructors for the concrete four-word native tuples. -/
def pack (counter first second third : Word) : WordTuple 4 :=
  .cons counter (.cons first (.cons second (.cons third .nil)))

def counter (values : WordTuple 4) : Word := values.get .head

def first (values : WordTuple 4) : Word := values.get (.tail .head)

def bindBank (fr : Frame Reg) (values : WordTuple 4) : Frame Reg :=
  (((fr.set (.arg 4) (counter values)).set (.arg 5) (first values)).set
    (.arg 6) (values.get (.tail (.tail .head)))).set (.arg 7) (values.get (.tail (.tail (.tail .head))))

def testWord (old : WordTuple 4) : Word := ofBool (counter old != 0)

def headerFrame (fr : Frame Reg) (old : WordTuple 4) : Frame Reg :=
  (((fr.set (.node 0) 1).set (.node 1) (counter old - 1)).set (.node 2) 0).set (.node 3) (testWord old)

def ArgsMatch {args : List PortTy} (fr : Frame Reg) (input : Tuple (Val model.value) args) : Prop :=
  ∀ p : Port args wordPort, fr.get (.arg p.index) = some (input.get p)

def Routes.nextBank (routes : Routes) (input old : WordTuple 4) : WordTuple 4 :=
  let args := appendTuple old input
  routes.graph.latch model .backedge args (routes.graph.header.eval model args PUnit.unit)

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
