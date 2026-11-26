module

public import Silmaril.SSA.Peggy.FieldHeap.Defs

/-! # Executable reversion of a straight-line heap-token spine -/

@[expose] public section

namespace Silmaril.SSA.Peggy.FieldHeap.Linearize

open RVSDG (Port Tuple)
open Silmaril.Semantics.Operational (Environment)

abbrev ReadTypes (reads : Nat) : List (PEG.Ty DataSort) :=
  List.replicate reads readValueTy

abbrev Graph (params : List (PEG.Ty DataSort)) (reads nodes : Nat) :=
  PEG.Graph Op params (stateTy :: ReadTypes reads) nodes 0

abbrev Inputs (params : List (PEG.Ty DataSort)) := Tuple interpretation.Value params

abbrev Outputs (reads : Nat) :=
  Tuple (fun t => Option (interpretation.Value t)) (stateTy :: ReadTypes reads)

/-- A straight-line schedule. Each instruction executes after its prior.
The vertex IDs identify effects and name the registers filled by loads. -/
inductive Schedule (params : List (PEG.Ty DataSort)) (nodes : Nat) where
  | entry (state : Port params stateTy)
  | store (prior : Schedule params nodes) (id : Fin nodes) (field : Field)
      (receiver : Port params receiverTy) (value : Port params intTy)
  | load (prior : Schedule params nodes) (id : Fin nodes) (field : Field)
      (receiver : Port params receiverTy)

structure Execution (nodes : Nat) where
  state : State
  /-- A load register retains its scalar result, including a completed fault. -/
  loads : Environment (Fin nodes) (Option Int)

variable {params : List (PEG.Ty DataSort)} {reads nodes : Nat}

def Schedule.run (input : Inputs params) : Schedule params nodes → Execution nodes
  | .entry state => ⟨input.get state, Environment.empty⟩
  | .store prior _ f r v =>
    let previous := prior.run input
    { previous with state := setField previous.state (input.get r) f (input.get v) }
  | .load prior id f r =>
    let previous := prior.run input
    let loaded := getField previous.state (input.get r) f
    ⟨loaded.state, Environment.set previous.loads id loaded.value⟩

/-- The effect vertex IDs from last to first, following token predecessors. -/
def Schedule.effects : Schedule params nodes → List (Fin nodes)
  | .entry _ => []
  | .store prior id .. | .load prior id .. => id :: prior.effects

def Schedule.hasLoad (id : Fin nodes) : Schedule params nodes → Bool
  | .entry _ => false
  | .store prior .. => prior.hasLoad id
  | .load prior register .. => id == register || prior.hasLoad id

/-- The typed tuple records which load register each value port reads, in root order. -/
structure Program (params : List (PEG.Ty DataSort)) (reads nodes : Nat) where
  schedule : Schedule params nodes
  valueRoots : Tuple (fun _ => Fin nodes) (ReadTypes reads)

def observeLoads (execution : Execution nodes) :
    (k : Nat) → Tuple (fun _ => Fin nodes) (ReadTypes k) →
      Tuple (fun t => Option (interpretation.Value t)) (ReadTypes k)
  | 0, .nil => .nil
  | k + 1, .cons id rest =>
    .cons (execution.loads id) (observeLoads execution k rest)

/-- Execute the recovered schedule, then observe the final state and selected load values. -/
def Program.run (program : Program params reads nodes) (input : Inputs params) : Outputs reads :=
  let execution := program.schedule.run input
  .cons (some execution.state) (observeLoads execution reads program.valueRoots)

inductive Error where
  | demandOrder
  | stateSpine
  | unsequencedEffect
  | valueRoot
  deriving DecidableEq, Repr

/-- The small collection of node forms recognized by reversion. -/
inductive Row (params : List (PEG.Ty DataSort)) {nodes : Nat} (sort : Fin nodes → PEG.Ty DataSort) :
    PEG.Ty DataSort → Type where
  | param {t} (slot : Port params t) : Row params sort t
  | store (field : Field) (state : PEG.Ref sort stateTy) (receiver : PEG.Ref sort receiverTy)
      (value : PEG.Ref sort intTy) : Row params sort stateTy
  | load (field : Field) (state : PEG.Ref sort stateTy) (receiver : PEG.Ref sort receiverTy) :
      Row params sort readTy
  | readState (result : PEG.Ref sort readTy) : Row params sort stateTy
  | readValue (result : PEG.Ref sort readTy) : Row params sort readValueTy

variable {sort : Fin nodes → PEG.Ty DataSort} {t : PEG.Ty DataSort}

def Row.ofOp : {ins : List (PEG.Ty DataSort)} → {out : PEG.Ty DataSort} →
    Op ins out → Tuple (PEG.Ref sort) ins → Option (Row params sort out)
  | _, _, .setField f, .cons s (.cons r (.cons v .nil)) => some (.store f s r v)
  | _, _, .getField f, .cons s (.cons r .nil) => some (.load f s r)
  | _, _, .readState, .cons result .nil => some (.readState result)
  | _, _, .readValue, .cons result .nil => some (.readValue result)
  | _, _, .forwardRead, _ => none

def Row.ofNode : PEG.Node Op params (Fin 0) sort t → Option (Row params sort t)
  | ⟨_, .param p, _⟩ => some (.param p)
  | ⟨_, .op instr, args⟩ => Row.ofOp instr args
  | _ => none

def row (g : Graph params reads nodes) (ref : PEG.Ref g.sort t) : Option (Row params g.sort t) :=
  ref.typed ▸ Row.ofNode (g.node ref.id)

def parameter (g : Graph params reads nodes) (ref : PEG.Ref g.sort t) : Option (Port params t) :=
  match row g ref with
  | some (.param slot) => some slot
  | _ => none

/-- Trace the unique explicit token predecessor of the final state. A load is
sequenced by its state projection, even when its value is never observed. -/
def trace (g : Graph params reads nodes) :
    Nat → PEG.Ref g.sort stateTy → Option (Schedule params nodes)
  | 0, _ => none
  | fuel + 1, token =>
    match row g token with
    | some (.param slot) => some (.entry slot)
    | some (.store f s r v) =>
      (trace g fuel s).bind fun prior =>
        (parameter g r).bind fun receiver =>
          (parameter g v).map (.store prior token.id f receiver)
    | some (.readState result) =>
      match row g result with
      | some (.load f s r) =>
        (trace g fuel s).bind fun prior => (parameter g r).map (.load prior result.id f)
      | _ => none
    | _ => none

def isEffectOp : {ins : List (PEG.Ty DataSort)} → {out : PEG.Ty DataSort} → Op ins out → Bool
  | _, _, .setField _ | _, _, .getField _ | _, _, .forwardRead => true
  | _, _, .readState | _, _, .readValue => false

def isEffect (node : PEG.Node Op params (Fin 0) sort t) : Bool :=
  match node.label with
  | .op instr => isEffectOp instr
  | _ => false

/-- Every effect in the table must be on the traced spine, including effects
whose results were discarded. Forked heap versions cannot be silently dropped. -/
def covers (g : Graph params reads nodes) (schedule : Schedule params nodes) : Bool :=
  (List.finRange nodes).all fun i => !isEffect (g.node i) || schedule.effects.contains i

def selectValues (g : Graph params reads nodes) (schedule : Schedule params nodes) :
    (k : Nat) → Tuple (PEG.Ref g.sort) (ReadTypes k) →
      Option (Tuple (fun _ => Fin nodes) (ReadTypes k))
  | 0, .nil => some .nil
  | k + 1, .cons root rest =>
    match row g root with
    | some (.readValue result) =>
      if schedule.hasLoad result.id then
        (selectValues g schedule k rest).map (.cons result.id)
      else none
    | _ => none

/-- Revert a rank-ordered, loop-free PEG to one serial field schedule. The phase
can be supplied independently of vertex numbering. Both the phase and the
effect coverage are checked against the original graph. -/
def linearize (g : Graph params reads nodes) (phase : Fin nodes → Nat := Fin.val) :
    Except Error (Program params reads nodes) :=
  if PEG.DemandRank.check [.phase phase] g then
    let .cons stateRoot valueRoots := g.roots
    match trace g nodes stateRoot with
    | none => .error .stateSpine
    | some schedule =>
      if covers g schedule then
        match selectValues g schedule reads valueRoots with
        | none => .error .valueRoot
        | some values => .ok ⟨schedule, values⟩
      else .error .unsequencedEffect
  else .error .demandOrder

end Silmaril.SSA.Peggy.FieldHeap.Linearize
