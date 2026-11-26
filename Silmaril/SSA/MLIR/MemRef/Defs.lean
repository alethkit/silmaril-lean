module

public import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.StraightLine.Defs
public import Mathlib.Logic.Function.Basic
public import Init.Data.BitVec

/-! One initialized, statically sized, contiguous rank-one MemRef of i64 cells. -/

@[expose] public section

namespace Silmaril.MLIR.MemRef

open SSA.RVSDG (Dialect Locals PortType Tuple)
open SSA.RVSDG.OrderedRuntime.Structured (Model Values)
open SSA.RVSDG.MLIR.Graph.Feedback (Code)

abbrev Word := BitVec 64

inductive ValueType (cells : Nat) where
  | index
  | i64
  | memref

/-- The sole reference available at the block boundary. The cell count
is part of its type. -/
inductive Reference (cells : Nat) where
  | entry

structure Buffer (cells : Nat) where
  cell : Fin cells → Word

def Value (cells : Nat) : ValueType cells → Type
  | .index => Fin cells
  | .i64 => Word
  | .memref => Reference cells

abbrev Ty (cells : Nat) := PortType (ValueType cells) PUnit
abbrev wordPorts (cells : Nat) : List (Ty cells) := [.value .i64]

/-- The load takes a reference and index. The store takes the word,
reference and index, and binds no SSA result. -/
inductive Op (cells : Nat) : Dialect (ValueType cells) PUnit where
  | load : Op cells [.value .memref, .value .index] (wordPorts cells)
  | store : Op cells [.value .i64, .value .memref, .value .index] []

def Op.name {cells : Nat} {ins outs : List (Ty cells)} : Op cells ins outs → String
  | .load => "memref.load"
  | .store => "memref.store"

abbrev NoPure (cells : Nat) : Dialect (ValueType cells) PUnit := fun _ _ => PEmpty

/-- The ordered runtime is a single initialized buffer. Index operands
are in bounds by construction. -/
def model (cells : Nat) : Model (NoPure cells) (Op cells) (StateM (Buffer cells)) where
  value := Value cells
  runPure op := nomatch op
  effect
    | .load, .cons _ (.cons index .nil) =>
      fun buffer => (.cons (buffer.cell index) .nil, buffer)
    | .store, .cons value (.cons _ (.cons index .nil)) =>
      fun buffer => (.nil, ⟨Function.update buffer.cell index value⟩)

abbrev Block (cells : Nat) (scope : List (List (Ty cells))) (outs : List (Ty cells)) :=
  {code : Code (Op cells) scope outs // code.StraightLine}

def run {cells : Nat} {scope : List (List (Ty cells))} {outs : List (Ty cells)}
    (block : Block cells scope outs) (env : Locals (Values (Value cells)) scope) :
    StateM (Buffer cells) (Tuple (Values (Value cells)) outs) :=
  block.val.runStraightLine (model cells).effect block.property env

end Silmaril.MLIR.MemRef
