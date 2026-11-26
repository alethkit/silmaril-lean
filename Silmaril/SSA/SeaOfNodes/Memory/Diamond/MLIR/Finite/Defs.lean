module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Defs
public import Silmaril.SSA.MLIR.SCF.For.Defs
public import Mathlib.Data.Nat.Log

/-! A finite-cell heap represented by an indexed list of scalar SSA values. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite

open RVSDG (Locals Origin Port Tuple)
open SeaOfNodes.Diamond (Slot)
open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.Pure (Code Eval Operands i1)
open Silmaril.MLIR.CF (Block Cfg Terminator)
open Silmaril.MLIR.SCF.For (weakenVar)

/-- The chosen signless address type must represent every cell index. -/
structure Profile where
  cells : Nat
  addressWidth : Width
  fits : cells ≤ 2 ^ addressWidth.val

/-- Every finite cell count has a profile, using the least positive width
that represents all its addresses. -/
def Profile.ofCells (cells : Nat) : Profile where
  cells := cells
  addressWidth := ⟨max 1 (Nat.clog 2 cells), Nat.lt_of_lt_of_le (by decide) (Nat.le_max_left _ _)⟩
  fits := (Nat.le_pow_clog (by decide : 1 < 2) cells).trans
    (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_max_right _ _))

variable {p : Profile} {args : List ValueSort} {past : List (List ValueSort)} {Γ Δ : List Width}

def encodeAddress (p : Profile) (address : Address p.cells) : BitVec p.addressWidth.val :=
  BitVec.ofNat _ address.val

abbrev sortWidth (p : Profile) : ValueSort → Width
  | .address => p.addressWidth
  | .word => i64

def encodeValue (p : Profile) : {sort : ValueSort} → Val p.cells sort → BitVec (sortWidth p sort).val
  | .address, address => encodeAddress p address
  | .word, word => word

/-- The scalar fragment uses `arith.constant`, `arith.cmpi eq` and `arith.select`. -/
inductive Op : Silmaril.MLIR.Pure.OpSignature where
  | constant (width : Width) (bits : BitVec width.val) : Op [] width
  | equal (width : Width) : Op [width, width] i1
  | select : Op [i1, i64, i64] i64

def evalOp : Eval Op
  | _, _, .constant _ bits, .nil => bits
  | _, _, .equal _, .cons lhs (.cons rhs .nil) => BitVec.ofBool (decide (lhs = rhs))
  | _, _, .select, inputs => MLIR.evalOp .select inputs

abbrev heapTypes (cells : Nat) := List.replicate cells i64
abbrev resultTypes (p : Profile) : List Width := i64 :: heapTypes p.cells
abbrev entryTypes (p : Profile) (args : List ValueSort) : List Width :=
  i1 :: (heapTypes p.cells ++ args.map (sortWidth p))

def encodeHeap : {cells : Nat} → Heap cells → Env (heapTypes cells)
  | 0, _ => .nil
  | _ + 1, heap => .cons (heap 0) (encodeHeap (fun index => heap index.succ))

def encodeScalars (p : Profile) : {args : List ValueSort} →
    Tuple (Val p.cells) args → Env (args.map (sortWidth p))
  | _, .nil => .nil
  | _, .cons value rest => .cons (encodeValue p value) (encodeScalars p rest)

def encodeEntry (p : Profile) (guard : Bool) (input : Tuple (Val p.cells) args)
    (heap : Heap p.cells) : Env (entryTypes p args) :=
  .cons (BitVec.ofBool guard) ((encodeHeap heap).append (encodeScalars p input))

def encodeResult (p : Profile) (word : Word) (heap : Heap p.cells) : Env (resultTypes p) :=
  .cons word (encodeHeap heap)

/-- A typed name for each current cell, in index order. -/
abbrev HeapRefs (cells : Nat) (Γ : List Width) := Fin cells → Var Γ i64

def heapOperands : {cells : Nat} → HeapRefs cells Γ → Operands Γ (heapTypes cells)
  | 0, _ => .nil
  | _ + 1, refs => .cons (refs 0) (heapOperands (fun index => refs index.succ))

def resultOperands (word : Var Γ i64) (heap : HeapRefs p.cells Γ) : Operands Γ (resultTypes p) :=
  .cons word (heapOperands heap)

abbrev Rename (Γ Δ : List Width) := ∀ {w}, Var Γ w → Var Δ w
abbrev Routing (p : Profile) (args : List ValueSort) (past : List (List ValueSort)) (Γ : List Width) :=
  ∀ {sort}, Origin args past sort → Var Γ (sortWidth p sort)

/-- The target names resolve every typed source wire in the supplied environment. -/
def Matches (route : Routing p args past Γ) (env : Env Γ)
    (input : Tuple (Val p.cells) args) (locals : Locals (Val p.cells) past) : Prop :=
  ∀ {sort} (wire : Origin args past sort),
    env.get (route wire) = encodeValue p (readValue wire input locals)

/-- The target names resolve all cells of the supplied native heap. -/
def HeapAgrees (refs : HeapRefs p.cells Γ) (env : Env Γ) (heap : Heap p.cells) : Prop :=
  ∀ index, env.get (refs index) = heap index

def Routing.rename (route : Routing p args past Γ) (widen : Rename Γ Δ) : Routing p args past Δ :=
  fun wire => widen (route wire)

def loadedVar {sort : ValueSort} (word : Var Δ i64) : Port [.word] sort → Var Δ (sortWidth p sort)
  | .head => word
  | .tail impossible => nomatch impossible

def Routing.afterLoad (route : Routing p args past Γ) (widen : Rename Γ Δ) (word : Var Δ i64) :
    Routing p args ([.word] :: past) Δ
  | _, .arg port => widen (route (.arg port))
  | sort, .output index port =>
    Fin.cases (motive := fun j => Port ([.word] :: past)[j] sort → Var Δ (sortWidth p sort))
      (loadedVar word) (fun j q => widen (route (.output j q))) index port

/-- Compare a dynamic address to a constant cell index, then emit one scalar select. -/
def selectCell {Term : List Width → Type} (index : Address p.cells)
    (address : Var Γ p.addressWidth) (onMatch otherwise : Var Γ i64)
    (next : Code Op Term (i64 :: i1 :: p.addressWidth :: Γ)) : Code Op Term Γ :=
  .letOp (.constant p.addressWidth (encodeAddress p index)) .nil
    (.letOp (.equal p.addressWidth) (.cons (.there address) (.cons .here .nil))
      (.letOp .select (.cons .here
        (.cons (.there (.there onMatch)) (.cons (.there (.there otherwise)) .nil))) next))

def underSelect {w : Width} (ref : Var Γ w) : Var (i64 :: i1 :: p.addressWidth :: Γ) w :=
  .there (.there (.there ref))

/-- Scan a fixed list of cell indices in the compiler, emitting scalar code. -/
def loadCells {Term : List Width → Type} :
    List (Address p.cells) → {Γ : List Width} → Var Γ p.addressWidth →
    HeapRefs p.cells Γ → Var Γ i64 →
    (∀ {Δ}, Rename Γ Δ → Var Δ i64 → Code Op Term Δ) → Code Op Term Γ
  | [], _, _, _, fallback, finish => finish (fun ref => ref) fallback
  | index :: rest, _, address, heap, fallback, finish =>
    selectCell index address (heap index) fallback
      (loadCells rest (underSelect address) (fun j => underSelect (heap j)) .here
        (fun widen word => finish (fun ref => widen (underSelect ref)) word))

def storeCells {Term : List Width → Type} :
    List (Address p.cells) → {Γ : List Width} → Var Γ p.addressWidth →
    Var Γ i64 → HeapRefs p.cells Γ →
    (∀ {Δ}, Rename Γ Δ → HeapRefs p.cells Δ → Code Op Term Δ) → Code Op Term Γ
  | [], _, _, _, heap, finish => finish (fun ref => ref) heap
  | index :: rest, _, address, word, heap, finish =>
    selectCell index address word (heap index)
      (storeCells rest (underSelect address) (underSelect word)
        (Function.update (fun j => underSelect (heap j)) index .here)
        (fun widen refs => finish (fun ref => widen (underSelect ref)) refs))

abbrev Finish (p : Profile) (Term : List Width → Type) :=
  ∀ {Δ}, Var Δ i64 → HeapRefs p.cells Δ → Term Δ

/-- Scalarize each Load and Store while threading the native ordered memory. -/
def lowerBody {Term : List Width → Type} (finish : Finish p Term) :
    {past : List (List ValueSort)} → {version : Nat} → Memory.Body args past version →
    {Γ : List Width} → Routing p args past Γ → HeapRefs p.cells Γ → Code Op Term Γ
  | _, _, .ret _ word, _, route, heap => .terminator (finish (route word) heap)
  | _, _, .load _ address rest, _, route, heap =>
    .letOp (.constant i64 0) .nil
      (loadCells (List.finRange p.cells) (.there (route address)) (fun j => .there (heap j)) .here
        (fun widen word =>
          lowerBody finish rest (route.afterLoad (fun ref => widen (.there ref)) word)
            (fun j => widen (.there (heap j)))))
  | _, _, .store _ address word rest, _, route, heap =>
    storeCells (List.finRange p.cells) (route address) (route word) heap
      (fun widen refs => lowerBody finish rest (route.rename widen) refs)

def appendVar {w : Width} (suffix : List Width) : {Γ : List Width} → Var Γ w → Var (Γ ++ suffix) w
  | _, .here => .here
  | _, .there ref => .there (appendVar suffix ref)

def cellVar : {cells : Nat} → Fin cells → Var (heapTypes cells) i64
  | 0, index => index.elim0
  | _ + 1, index => Fin.cases .here (fun j => .there (cellVar j)) index

def argVar {sort : ValueSort} : {args : List ValueSort} →
    Port args sort → Var (args.map (sortWidth p)) (sortWidth p sort)
  | _, .head => .here
  | _, .tail port => .there (argVar port)

def entryRoute (p : Profile) (args : List ValueSort) : Routing p args [] (entryTypes p args)
  | _, .arg port => .there (weakenVar (argVar port) (heapTypes p.cells))
  | _, .output index _ => index.elim0

def entryHeap (p : Profile) (args : List ValueSort) : HeapRefs p.cells (entryTypes p args) :=
  fun index => .there (appendVar (args.map (sortWidth p)) (cellVar index))

def joinRoute (p : Profile) (args : List ValueSort) :
    Routing p (.word :: args) [] (resultTypes p ++ entryTypes p args)
  | _, .arg .head => .here
  | _, .arg (.tail port) => weakenVar (entryRoute p args (.arg port)) (resultTypes p)
  | _, .output index _ => index.elim0

def joinHeap (p : Profile) (args : List ValueSort) :
    HeapRefs p.cells (resultTypes p ++ entryTypes p args) :=
  fun index => appendVar (entryTypes p args) (.there (cellVar index))

inductive Label (p : Profile) : List Width → Type where
  | arm (slot : Slot) : Label p []
  | join : Label p (resultTypes p)

def armBlock (p : Profile) (graph : Graph args) (slot : Slot) :
    Block Op (Label p) (entryTypes p args) (resultTypes p) :=
  lowerBody (fun word heap => .br ⟨.join, resultOperands word heap⟩)
    (graph.arm (graph.merge.predecessor slot)) (entryRoute p args) (entryHeap p args)

def joinBlock (p : Profile) (graph : Graph args) :
    Block Op (Label p) (resultTypes p ++ entryTypes p args) (resultTypes p) :=
  lowerBody (fun word heap => .ret (resultOperands word heap))
    graph.suffix (joinRoute p args) (joinHeap p args)

/-- Use the actual CF branch to select a source occurrence, and forward the
exported word and all indexed cell values as join arguments. -/
def lower (p : Profile) (graph : Graph args) : Cfg Op (Label p) (entryTypes p args) (resultTypes p) where
  entry := .terminator (.condBr .here
    ⟨.arm (graph.merge.slot .onTrue), .nil⟩ ⟨.arm (graph.merge.slot .onFalse), .nil⟩)
  block
    | .arm slot => armBlock p graph slot
    | .join => joinBlock p graph

/-- The entry, selected arm and suffix each consume one block tick. -/
def observe (p : Profile) (graph : Graph args) (guard : Bool) (input : Tuple (Val p.cells) args)
    (initial : Heap p.cells) : Option (Env (resultTypes p)) :=
  (lower p graph).run evalOp 3 (encodeEntry p guard input initial)

def Returns (p : Profile) (graph : Graph args) (guard : Bool) (input : Tuple (Val p.cells) args)
    (initial : Heap p.cells) (word : Word) (final : Heap p.cells) : Prop :=
  ∃ fuel, (lower p graph).run evalOp fuel (encodeEntry p guard input initial) =
    some (encodeResult p word final)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite
