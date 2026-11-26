module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Defs
public import Silmaril.SSA.PhiView.Defs

/-! # An effectful λSSA CFG for the whole-memory diamond -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA

open SeaOfNodes.Diamond (Projection Slot)
open RVSDG (Locals Origin Port Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Region Terminator Tm)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

abbrev Code := Silmaril.Ty ValueSort
abbrev wordCode : Code := .base .word
abbrev guardCode : Code := .coprod .unit .unit
abbrev wordPacket : Code := PhiView.packedType [wordCode]

inductive Opcode where
  | load
  | store

instance : HasTy Opcode Code where
  src
    | .load => .base .address
    | .store => .product (.base .address) wordCode
  trg
    | .load => wordCode
    | .store => .unit

abbrev Atom (cells : Nat) := Address cells ⊕ Word

def encode {cells : Nat} : {sort : ValueSort} → Val cells sort → Value (Atom cells)
  | .address, address => .atom (.inl address)
  | .word, word => .atom (.inr word)

def packet {cells : Nat} (word : Word) : Value (Atom cells) :=
  .pair (encode (sort := .word) word) .unit

/-- The ambient state is the whole heap. A load leaves it intact and a store
uses the shared heap update, returning unit as its scalar result. -/
inductive Instruction (cells : Nat) :
    Opcode → Value (Atom cells) → Heap cells → Value (Atom cells) → Heap cells → Prop where
  | load (address : Address cells) (heap : Heap cells) :
      Instruction cells .load (encode (sort := .address) address) heap
        (encode (sort := .word) (heap.read address)) heap
  | store (address : Address cells) (word : Word) (heap : Heap cells) :
      Instruction cells .store
        (.pair (encode (sort := .address) address) (encode (sort := .word) word)) heap
        .unit (heap.write address word)

def inputEnv {cells : Nat} : {args : List ValueSort} → Tuple (Val cells) args → Env (Atom cells)
  | _, .nil => fun _ => .unit
  | _, .cons value rest => extend (inputEnv rest) (encode value)

def guardValue {cells : Nat} (guard : Bool) : Value (Atom cells) :=
  if guard then .inl .unit else .inr .unit

def entryEnv {cells : Nat} {args : List ValueSort} (guard : Bool) (input : Tuple (Val cells) args) :
    Env (Atom cells) :=
  extend (inputEnv input) (guardValue guard)

abbrev entryContext (args : List ValueSort) : List Code := guardCode :: args.map Silmaril.Ty.base

abbrev Ref (context : List Code) (sort : ValueSort) :=
  PhiView.Operand context (.base sort)

variable {args : List ValueSort} {past : List (List ValueSort)} {context : List Code}
variable {cells version : Nat}

def shift {sort : ValueSort} (A : Code) (ref : Ref context sort) : Ref (A :: context) sort :=
  ⟨ref.val + 1, ref.property⟩

def argumentRef {sort : ValueSort} : {args : List ValueSort} →
    Port args sort → Ref (args.map Silmaril.Ty.base) sort
  | _, .head => ⟨0, rfl⟩
  | _, .tail p => shift _ (argumentRef p)

/-- Resolve a source scalar origin in the current λSSA context. Memory
versions use the ambient heap and have no scalar indices. -/
abbrev Routing (args : List ValueSort) (past : List (List ValueSort)) (context : List Code) :=
  ∀ {sort}, Origin args past sort → Ref context sort

def Routing.entry (args : List ValueSort) : Routing args [] (args.map Silmaril.Ty.base)
  | _, .arg p => argumentRef p
  | _, .output i _ => i.elim0

def Routing.weaken (A : Code) (route : Routing args past context) : Routing args past (A :: context) :=
  fun wire => shift A (route wire)

def loadedRef {sort : ValueSort} : Port [.word] sort → Ref (wordCode :: context) sort
  | .head => ⟨0, rfl⟩
  | .tail impossible => nomatch impossible

def Routing.afterLoad (route : Routing args past context) :
    Routing args ([.word] :: past) (wordCode :: context)
  | _, .arg p => shift wordCode (route (.arg p))
  | sort, .output i p =>
    Fin.cases (motive := fun j => Port ([.word] :: past)[j] sort → Ref (wordCode :: context) sort)
      loadedRef (fun j port => shift wordCode (route (.output j port))) i p

/-- The target environment realizes every scalar origin of the source body. -/
def Matches (route : Routing args past context) (env : Env (Atom cells))
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) : Prop :=
  ∀ {sort} (wire : Origin args past sort),
    env (route wire).val = encode (readValue wire input locals)

/-- Keep the emitted lets and the typed Return operand together. -/
structure Schedule where
  statements : Isotope.LambdaSSA.Body Opcode
  context : List Code
  result : Ref context .word

def schedule : {past : List (List ValueSort)} → {version : Nat} →
    Memory.Body args past version → {context : List Code} → Routing args past context → Schedule
  | _, _, .ret _ source, context, route => ⟨.nil, context, route source⟩
  | _, _, .load _ address rest, _, route =>
    let tail := schedule rest (Routing.afterLoad route)
    { tail with statements := .let₁ (.op .load (.var (route address).val)) tail.statements }
  | _, _, .store _ address source rest, _, route =>
    let tail := schedule rest (Routing.weaken .unit route)
    let value : Tm Opcode := .op .store (.pair (.var (route address).val) (.var (route source).val))
    { tail with statements := .let₁ value tail.statements }

def Schedule.arguments (body : Schedule) : PhiView.Arguments body.context [wordCode] :=
  fun i => Fin.cases body.result (fun j => j.elim0) i

def Schedule.terminator (body : Schedule) (label : Nat) : Terminator Opcode :=
  .br label (PhiView.packTerm body.arguments)

def prepend : Isotope.LambdaSSA.Body Opcode → Region Opcode → Region Opcode
  | .nil, tail => tail
  | .let₁ rhs rest, tail => .let₁ rhs (prepend rest tail)
  | .let₂ rhs rest, tail => .let₂ rhs (prepend rest tail)

def Schedule.emit (body : Schedule) (label : Nat) : Region Opcode :=
  prepend body.statements (.br label (PhiView.packTerm body.arguments))

def armRouting (args : List ValueSort) : Routing args [] (.unit :: entryContext args) :=
  Routing.entry args |> Routing.weaken guardCode |> Routing.weaken .unit

/-- The suffix sees the join word and the captured scalar inputs. The join
packet, unit field, and original guard occupy the other slots. -/
def suffixRouting (args : List ValueSort) :
    Routing (.word :: args) [] (.unit :: wordCode :: wordPacket :: entryContext args)
  | _, .arg .head => ⟨1, rfl⟩
  | _, .arg (.tail p) =>
    let route := Routing.entry args |> Routing.weaken guardCode |> Routing.weaken wordPacket
      |> Routing.weaken wordCode |> Routing.weaken .unit
    route (.arg p)
  | _, .output i _ => i.elim0

variable (g : Graph args)

def armSchedule (p : Projection) : Schedule := schedule (g.arm p) (armRouting args)

def armTerminator (p : Projection) : Terminator Opcode := (armSchedule g p).terminator 2

def sourceTyping : PhiView.SourceTyping (τ := Code) (armTerminator g) where
  context p := (armSchedule g p).context
  cases _ := .jump

def parameters : Nat → List Code
  | 2 => [wordCode]
  | _ => []

def blockArgs : PhiView.BlockArgs (sourceTyping g) parameters
  | ⟨p, .jump⟩ => ⟨(armSchedule g p).arguments, rfl⟩

def phiView : PhiView.View (sourceTyping g) parameters := PhiView.ofBlockArgs (blockArgs g)

def incoming (p : Projection) : PhiView.EdgeOcc (armTerminator g) := ⟨p, .jump⟩

def edge (slot : Slot) : PhiView.EdgeOcc (armTerminator g) := incoming g (g.merge.predecessor slot)

def dispatch : Region Opcode := .case (.var 0) (.br 0 .unit) (.br 1 .unit)

def blockTypes : Fin 3 → Code :=
  Fin.cases .unit (Fin.cases .unit (fun _ => wordPacket))

def suffix : Region Opcode := .let₂ (.var 0) ((schedule g.suffix (suffixRouting args)).emit 3)

def blocks : Fin 3 → Region Opcode :=
  Fin.cases ((armSchedule g .onTrue).emit 2)
    (Fin.cases ((armSchedule g .onFalse).emit 2) (fun _ => suffix g))

/-- Each arm enters the same join with its packed word and the heap left by
its instructions. The join runs the common suffix in that heap. -/
def lower : Region Opcode := .cfg dispatch 3 (blocks g)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA
