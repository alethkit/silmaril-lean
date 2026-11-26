module

public import Silmaril.Machine.SeaOfNodes.Diamond.RTL.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Defs
public import Silmaril.SSA.RVSDG.Isomorphism.Defs

/-! # Typed word columns and routed all-i64 RTL loops -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing

open Silmaril.Machine.Lir (Binop Word ofBool)
open Silmaril.Machine.RTL.SSA (Block Func Prog)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp emitOpsWith model word)
open Silmaril.SSA.RVSDG (Address Origin Port Tuple Wires extend)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Val dataPorts)
open Silmaril.SSA.SeaOfNodes.Loop (Graph Incoming appendTuple)

abbrev wordPort : PortTy := .value word
abbrev wordSorts (n : Nat) := List.replicate n word
abbrev wordPorts (n : Nat) : List PortTy := dataPorts (wordSorts n)
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

abbrev headerSigs : List (List PortTy) := [[wordPort], [wordPort], [wordPort], [.value .predicate]]

theorem wordPorts_eq_replicate (n : Nat) : wordPorts n = List.replicate n wordPort := by
  simp [List.map_replicate]

theorem wordPorts_append (m n : Nat) : wordPorts (m + n) = wordPorts m ++ wordPorts n := by
  simp only [wordPorts_eq_replicate, List.replicate_add]

def prefixPort {pre tail : List PortTy} {t : PortTy} : Port pre t → Port (pre ++ tail) t
  | .head => .head
  | .tail p => .tail (prefixPort p)

def suffixPort {tail : List PortTy} {t : PortTy} :
    (pre : List PortTy) → Port tail t → Port (pre ++ tail) t
  | [], p => p
  | _ :: rest, p => .tail (suffixPort rest p)

/-- The counter occupies slot zero in each tuple. Payload routes may read
any visible argument. A typed result selects one of the carried payloads. -/
structure BankRoutes (payloads : Nat) where
  entry : ArgumentColumn (payloads + 1) payloads
  feedback : Wires (wordPorts (payloads + 1) ++ wordPorts (payloads + 1)) [] (wordPorts payloads)
  result : Fin payloads

def checkBankRoutes (payloads : Nat) (entry feedback : List Nat) (result : Nat) :
    Option (BankRoutes payloads) :=
  if valid : result < payloads then
    (checkColumn (payloads + 1) payloads entry).bind fun initial =>
      (checkColumn ((payloads + 1) + (payloads + 1)) payloads feedback).map fun next =>
        ⟨initial, wordPorts_append (payloads + 1) (payloads + 1) ▸ next, ⟨result, valid⟩⟩
  else none

def BankRoutes.resultPort {payloads : Nat} (r : BankRoutes payloads) :
    Port (wordPorts (payloads + 1)) wordPort :=
  .tail (argumentPort payloads r.result)

def counterPort (payloads : Nat) :
    Port (wordPorts (payloads + 1) ++ wordPorts (payloads + 1)) wordPort :=
  suffixPort (wordPorts (payloads + 1)) .head

/-- The computed route adds one total word instruction to the countdown
header. Its operands and destination refer to payload slots, with slot zero
of the whole carried tuple still reserved for the counter. -/
inductive FeedbackOp
  | add
  | sub

def FeedbackOp.source : FeedbackOp → WordOp [word, word] word
  | .add => .add
  | .sub => .sub

def FeedbackOp.target : FeedbackOp → Binop
  | .add => .add
  | .sub => .sub

def FeedbackOp.eval : FeedbackOp → Word → Word → Word
  | .add => BitVec.add
  | .sub => BitVec.sub

structure FeedbackSpec where
  operation : FeedbackOp
  destination : Nat
  left : Nat
  right : Nat

structure FeedbackUpdate (payloads : Nat) where
  operation : FeedbackOp
  destination : Fin payloads
  left : Fin payloads
  right : Fin payloads

def FeedbackSpec.check (spec : FeedbackSpec) (payloads : Nat) : Option (FeedbackUpdate payloads) :=
  if dest : spec.destination < payloads then
    if left : spec.left < payloads then
      if right : spec.right < payloads then
        some ⟨spec.operation, ⟨spec.destination, dest⟩, ⟨spec.left, left⟩, ⟨spec.right, right⟩⟩
      else none
    else none
  else none

def payloadPort (payloads : Nat) (p : Fin payloads) :
    Port (wordPorts (payloads + 1)) wordPort :=
  .tail (argumentPort payloads p)

def oldPayloadPort (payloads : Nat) (p : Fin payloads) :
    Port (wordPorts (payloads + 1) ++ wordPorts (payloads + 1)) wordPort :=
  suffixPort (wordPorts (payloads + 1)) (payloadPort payloads p)

def FeedbackUpdate.eval {payloads : Nat} (update : FeedbackUpdate payloads)
    (old : WordTuple (payloads + 1)) : Word :=
  update.operation.eval (old.get (payloadPort payloads update.left))
    (old.get (payloadPort payloads update.right))

def extraSigs {payloads : Nat} : Option (FeedbackUpdate payloads) → List (List PortTy)
  | none => []
  | some _ => [[wordPort]]

abbrev headerSigsWith {payloads : Nat} (update : Option (FeedbackUpdate payloads)) :=
  headerSigs ++ extraSigs update

def headerSuffix {payloads : Nat} (update : Option (FeedbackUpdate payloads)) :
    Dataflow WordOp (wordPorts (payloads + 1) ++ wordPorts (payloads + 1))
      headerSigs (extraSigs update) :=
  match update with
  | none => .nil
  | some u =>
    .cons u.operation.source
      (.cons (.arg (oldPayloadPort payloads u.left))
        (.cons (.arg (oldPayloadPort payloads u.right)) .nil)) .nil

def replaceWire {args users : List PortTy} {past : List (List PortTy)} {t : PortTy}
    (value : Origin args past t) (wires : Wires args past users) (slot : Port users t) :
    Wires args past users :=
  match slot, wires with
  | .head, .cons _ rest => .cons value rest
  | .tail slot, .cons w rest => .cons w (replaceWire value rest slot)

def BankRoutes.feedbackWith {payloads : Nat} (r : BankRoutes payloads)
    (update : Option (FeedbackUpdate payloads)) :
    Wires (wordPorts (payloads + 1) ++ wordPorts (payloads + 1))
      (extend [] (headerSigsWith update)) (wordPorts (payloads + 1)) :=
  match update with
  | none => .cons (.output (1 : Fin 4) .head) (extendArguments _ r.feedback)
  | some u => .cons (.output (1 : Fin 5) .head)
      (replaceWire (.output (4 : Fin 5) .head) (extendArguments _ r.feedback)
        (argumentPort payloads u.destination))

def BankRoutes.graphWith {payloads : Nat} (r : BankRoutes payloads)
    (update : Option (FeedbackUpdate payloads)) :
    Graph WordOp (wordSorts (payloads + 1)) (wordSorts (payloads + 1)) []
      (headerSigsWith update) word where
  preheader := .nil
  header :=
    .cons (.const 1) .nil
      (.cons .sub (.cons (.arg (counterPort payloads)) (.cons (.output (0 : Fin 1) .head) .nil))
        (.cons (.const 0) .nil
          (.cons .ne (.cons (.arg (counterPort payloads)) (.cons (.output (2 : Fin 3) .head) .nil))
            (headerSuffix update))))
  phiInputs
    | .entry => .cons (.arg .head) r.entry
    | .backedge => r.feedbackWith update
  predicate := match update with
    | none => .output (3 : Fin 4) .head
    | some _ => .output (3 : Fin 5) .head
  result := .arg (suffixPort (wordPorts (payloads + 1)) r.resultPort)

def BankRoutes.incomingWith {payloads : Nat} (r : BankRoutes payloads)
    (update : Option (FeedbackUpdate payloads)) : Incoming → List Reg
  | .entry => emitColumn (arity := payloads + 1) ((r.graphWith update).phiInputs .entry)
  | .backedge => emitColumn (arity := payloads + 1) ((r.graphWith update).phiInputs .backedge)

def paramRegs (base arity : Nat) : List Reg := (List.range' base arity).map Reg.arg

def BankRoutes.preheaderWith {payloads : Nat} (r : BankRoutes payloads)
    (update : Option (FeedbackUpdate payloads)) : Block Reg :=
  ⟨paramRegs 0 (payloads + 1), [], .jump 1 (r.incomingWith update .entry)⟩

def BankRoutes.headerWith {payloads : Nat} (r : BankRoutes payloads)
    (update : Option (FeedbackUpdate payloads)) : Block Reg :=
  let graph := r.graphWith update
  ⟨paramRegs (payloads + 1) (payloads + 1), emitOpsWith (fun p => .arg p.index) graph.header,
    .cond (register graph.predicate.address) 1 (r.incomingWith update .backedge)
      2 [register graph.result.address]⟩

def exitBlock : Block Reg := ⟨[.phi], [], .ret [.phi]⟩

def BankRoutes.lowerFuncWith {payloads : Nat} (r : BankRoutes payloads)
    (update : Option (FeedbackUpdate payloads)) : Func Reg :=
  ⟨⟨payloads + 1, 1⟩, 0, [r.preheaderWith update, r.headerWith update, exitBlock]⟩

def BankRoutes.lowerWith {payloads : Nat} (r : BankRoutes payloads)
    (update : Option (FeedbackUpdate payloads)) : Prog Reg :=
  ⟨[r.lowerFuncWith update]⟩

abbrev BankRoutes.graph {payloads : Nat} (r : BankRoutes payloads) := r.graphWith none
abbrev BankRoutes.incomingRegisters {payloads : Nat} (r : BankRoutes payloads) := r.incomingWith none
abbrev BankRoutes.preheader {payloads : Nat} (r : BankRoutes payloads) := r.preheaderWith none
abbrev BankRoutes.header {payloads : Nat} (r : BankRoutes payloads) := r.headerWith none
abbrev BankRoutes.lowerFunc {payloads : Nat} (r : BankRoutes payloads) := r.lowerFuncWith none
abbrev BankRoutes.lower {payloads : Nat} (r : BankRoutes payloads) := r.lowerWith none

/-- A zero-payload bank is rejected because it has no payload return port. -/
def lowerBankChecked (payloads : Nat) (entry feedback : List Nat) (result : Nat) : Option (Prog Reg) :=
  (checkBankRoutes payloads entry feedback result).bind fun routes =>
    if routes.lowerFunc.WellFormed then some routes.lower else none

/-- Start from a checked copy plan, override one feedback destination with
the computed word, and check the emitted machine function. -/
def lowerComputedChecked (payloads : Nat) (entry feedback : List Nat) (result : Nat)
    (spec : FeedbackSpec) : Option (Prog Reg) :=
  (spec.check payloads).bind fun update =>
    (checkBankRoutes payloads entry feedback result).bind fun routes =>
      if (routes.lowerFuncWith (some update)).WellFormed then some (routes.lowerWith (some update))
      else none

def counter {payloads : Nat} (values : WordTuple (payloads + 1)) : Word := values.get .head

def bindWords (base : Nat) (fr : Frame Reg) : {arity : Nat} → WordTuple arity → Frame Reg
  | 0, .nil => fr
  | _ + 1, .cons w rest => bindWords (base + 1) (fr.set (.arg base) w) rest

def bindBank {payloads : Nat} (fr : Frame Reg) (values : WordTuple (payloads + 1)) : Frame Reg :=
  bindWords (payloads + 1) fr values

def testWord {payloads : Nat} (old : WordTuple (payloads + 1)) : Word := ofBool (counter old != 0)

def headerFrame {payloads : Nat} (fr : Frame Reg) (old : WordTuple (payloads + 1)) : Frame Reg :=
  (((fr.set (.node 0) 1).set (.node 1) (counter old - 1)).set (.node 2) 0).set (.node 3) (testWord old)

def headerFrameWith {payloads : Nat} (update : Option (FeedbackUpdate payloads))
    (fr : Frame Reg) (old : WordTuple (payloads + 1)) : Frame Reg :=
  match update with
  | none => headerFrame fr old
  | some u => (headerFrame fr old).set (.node 4) (u.eval old)

def ArgsMatch {args : List PortTy} (fr : Frame Reg) (input : Tuple (Val model.value) args) : Prop :=
  ∀ p : Port args wordPort, fr.get (.arg p.index) = some (input.get p)

def BankRoutes.nextBankWith {payloads : Nat} (r : BankRoutes payloads)
    (update : Option (FeedbackUpdate payloads)) (input old : WordTuple (payloads + 1)) :
    WordTuple (payloads + 1) :=
  let args := appendTuple old input
  let graph := r.graphWith update
  graph.latch model .backedge args (graph.header.eval model args PUnit.unit)

abbrev BankRoutes.nextBank {payloads : Nat} (r : BankRoutes payloads) := r.nextBankWith none

def BankRoutes.returnWord {payloads : Nat} (r : BankRoutes payloads) (old : WordTuple (payloads + 1)) : Word :=
  old.get r.resultPort

/-! The three-payload interface selects the first payload at exit. -/

abbrev inputSorts := wordSorts 4
abbrev carriedSorts := wordSorts 4

structure Routes where
  entry : ArgumentColumn 4 3
  feedback : ArgumentColumn 8 3

def Routes.toBankRoutes (r : Routes) : BankRoutes 3 := ⟨r.entry, r.feedback, 0⟩

def checkRoutes (entry feedback : List Nat) : Option Routes :=
  (checkColumn 4 3 entry).bind fun initial =>
    (checkColumn 8 3 feedback).map fun next => ⟨initial, next⟩

abbrev Routes.graph (r : Routes) := r.toBankRoutes.graph
abbrev Routes.incomingRegisters (r : Routes) := r.toBankRoutes.incomingRegisters
abbrev entryParams := paramRegs 0 4
abbrev bankParams := paramRegs 4 4
abbrev Routes.preheader (r : Routes) := r.toBankRoutes.preheader
abbrev Routes.header (r : Routes) := r.toBankRoutes.header
abbrev Routes.lowerFunc (r : Routes) := r.toBankRoutes.lowerFunc
abbrev Routes.lower (r : Routes) := r.toBankRoutes.lower
abbrev Routes.nextBank (r : Routes) := r.toBankRoutes.nextBank

def lowerChecked (entry feedback : List Nat) : Option (Prog Reg) :=
  (checkRoutes entry feedback).bind fun routes =>
    if routes.lowerFunc.WellFormed then some routes.lower else none

def pack (counter first second third : Word) : WordTuple 4 :=
  .cons counter (.cons first (.cons second (.cons third .nil)))

def first (values : WordTuple 4) : Word := values.get (.tail .head)

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
