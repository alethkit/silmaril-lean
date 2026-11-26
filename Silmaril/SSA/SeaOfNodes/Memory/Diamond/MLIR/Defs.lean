module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Defs
public import Silmaril.SSA.MLIR.CF.Basic.Defs

/-! Two initialized cells as typed scalar SSA values. Load and Store use
scalar `arith.select`; the CF join receives the selected word and both cells. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR

open RVSDG (Origin Port Tuple)
open SeaOfNodes.Diamond (Slot)
open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.Pure (Code Eval Operands i1)
open Silmaril.MLIR.CF (Block Cfg Terminator)

abbrev i64 : Width := ⟨64, by decide⟩

def firstCell : Address 2 := 0
def secondCell : Address 2 := 1

abbrev sortWidth : ValueSort → Width
  | .address => i1
  | .word => i64

def encodeValue : {sort : ValueSort} → Val 2 sort → BitVec (sortWidth sort).val
  | .address, address => BitVec.ofNat 1 address.val
  | .word, word => word

/-- Scalar `arith.select` for the specific condition and word widths. -/
inductive Op : Silmaril.MLIR.Pure.OpSignature where
  | select : Op [i1, i64, i64] i64

def selectWord (condition : BitVec 1) (onTrue onFalse : Word) : Word :=
  if condition.getLsbD 0 then onTrue else onFalse

def evalOp : Eval Op
  | _, _, .select, .cons condition (.cons onTrue (.cons onFalse .nil)) =>
    selectWord condition onTrue onFalse

abbrev resultTypes : List Width := [i64, i64, i64]
abbrev entryTypes (args : List ValueSort) : List Width := i1 :: i64 :: i64 :: args.map sortWidth

def encodeScalars : {args : List ValueSort} → Tuple (Val 2) args → Env (args.map sortWidth)
  | _, .nil => .nil
  | _, .cons value rest => .cons (encodeValue value) (encodeScalars rest)

def encodeEntry {args : List ValueSort} (guard : Bool) (input : Tuple (Val 2) args)
    (heap : Heap 2) : Env (entryTypes args) :=
  .cons (BitVec.ofBool guard) (.cons (heap firstCell) (.cons (heap secondCell) (encodeScalars input)))

def encodeResult (word : Word) (heap : Heap 2) : Env resultTypes :=
  .cons word (.cons (heap firstCell) (.cons (heap secondCell) .nil))

variable {args : List ValueSort} {past : List (List ValueSort)} {Γ : List Width}

abbrev Routing (args : List ValueSort) (past : List (List ValueSort)) (Γ : List Width) :=
  ∀ {sort}, Origin args past sort → Var Γ (sortWidth sort)

def Routing.weaken (width : Width) (route : Routing args past Γ) : Routing args past (width :: Γ) :=
  fun wire => .there (route wire)

def loadedVar {sort : ValueSort} : Port [.word] sort → Var (i64 :: Γ) (sortWidth sort)
  | .head => .here
  | .tail impossible => nomatch impossible

def Routing.afterLoad (route : Routing args past Γ) :
    Routing args ([.word] :: past) (i64 :: Γ)
  | _, .arg p => .there (route (.arg p))
  | sort, .output j p =>
    Fin.cases (motive := fun n =>
      Port ([.word] :: past)[n] sort → Var (i64 :: Γ) (sortWidth sort))
      loadedVar (fun n q => .there (route (.output n q))) j p

/-- References naming the two current cell values. -/
structure HeapRefs (Γ : List Width) where
  first : Var Γ i64
  second : Var Γ i64

def HeapRefs.weaken (width : Width) (heap : HeapRefs Γ) : HeapRefs (width :: Γ) :=
  ⟨.there heap.first, .there heap.second⟩

def resultOperands (word : Var Γ i64) (heap : HeapRefs Γ) : Operands Γ resultTypes :=
  .cons word (.cons heap.first (.cons heap.second .nil))

abbrev Finish (Term : List Width → Type) :=
  ∀ {Δ}, Var Δ i64 → HeapRefs Δ → Term Δ

/-- Lower ordered memory bindings into SSA. A load selects the current cell.
A store binds two new cell values, updating just the addressed cell. -/
def lowerBody {Term : List Width → Type} (finish : Finish Term) :
    {past : List (List ValueSort)} → {version : Nat} → Memory.Body args past version →
    {Γ : List Width} → Routing args past Γ → HeapRefs Γ → Code Op Term Γ
  | _, _, .ret _ word, _, route, heap => .terminator (finish (route word) heap)
  | _, _, .load _ address rest, _, route, heap =>
    .letOp .select (.cons (route address) (.cons heap.second (.cons heap.first .nil)))
      (lowerBody finish rest route.afterLoad (heap.weaken i64))
  | _, _, .store _ address value rest, _, route, heap =>
    .letOp .select (.cons (route address) (.cons heap.first (.cons (route value) .nil)))
      (.letOp .select
        (.cons (.there (route address)) (.cons (.there (route value)) (.cons (.there heap.second) .nil)))
        (lowerBody finish rest (Routing.weaken i64 (Routing.weaken i64 route)) ⟨.there .here, .here⟩))

def argVar {sort : ValueSort} : {args : List ValueSort} →
    Port args sort → Var (args.map sortWidth) (sortWidth sort)
  | _, .head => .here
  | _, .tail p => .there (argVar p)

def entryRoute (args : List ValueSort) : Routing args [] (entryTypes args)
  | _, .arg p => .there (.there (.there (argVar p)))
  | _, .output i _ => i.elim0

abbrev entryHeap (args : List ValueSort) : HeapRefs (entryTypes args) :=
  ⟨.there .here, .there (.there .here)⟩

def joinRoute (args : List ValueSort) : Routing (.word :: args) [] (resultTypes ++ entryTypes args)
  | _, .arg .head => .here
  | _, .arg (.tail p) => .there (.there (.there (entryRoute args (.arg p))))
  | _, .output i _ => i.elim0

abbrev joinHeap (args : List ValueSort) : HeapRefs (resultTypes ++ entryTypes args) :=
  ⟨.there .here, .there (.there .here)⟩

/-- Distinct source predecessor occurrences label distinct CF blocks. -/
inductive Label : List Width → Type where
  | arm (slot : Slot) : Label []
  | join : Label resultTypes

def armBlock (graph : Graph args) (slot : Slot) : Block Op Label (entryTypes args) resultTypes :=
  lowerBody (fun word heap => .br ⟨.join, resultOperands word heap⟩)
    (graph.arm (graph.merge.predecessor slot)) (entryRoute args) (entryHeap args)

def joinBlock (graph : Graph args) : Block Op Label (resultTypes ++ entryTypes args) resultTypes :=
  lowerBody (fun word heap => .ret (resultOperands word heap))
    graph.suffix (joinRoute args) (joinHeap args)

/-- Lower the actual diamond to a conditional branch, its two arms and a
shared suffix. The join's arguments carry the arm word and whole heap. -/
def lower (graph : Graph args) : Cfg Op Label (entryTypes args) resultTypes where
  entry := .terminator (.condBr .here
    ⟨.arm (graph.merge.slot .onTrue), .nil⟩ ⟨.arm (graph.merge.slot .onFalse), .nil⟩)
  block
    | .arm slot => armBlock graph slot
    | .join => joinBlock graph

/-- A finite return from the existing typed CF evaluator. -/
def Returns (graph : Graph args) (guard : Bool) (input : Tuple (Val 2) args)
    (initial : Heap 2) (word : Word) (final : Heap 2) : Prop :=
  ∃ fuel, (lower graph).run evalOp fuel (encodeEntry guard input initial) =
    some (encodeResult word final)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR
