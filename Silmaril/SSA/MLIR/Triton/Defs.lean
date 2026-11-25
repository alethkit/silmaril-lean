module

public import Silmaril.SSA.MLIR.Tensor.Defs

/-! # Logical Triton and Gluon tiles

This fragment has one tensor shape (`[64]`) and one element type (`i32`).
Triton expressions describe logical values. Gluon expressions carry explicit
blocked layouts and denote values indexed by lane and register slot.
-/

@[expose] public section

namespace Silmaril.MLIR.Triton

abbrev Tile := Tensor.Tensor [64] (BitVec 32)

/-- The nonnegative starts of `[start, start + 64)` whose exclusive end still
fits in signed `i32`. -/
abbrev RangeStart := Fin (2 ^ 31 - 64)

/-- A pure expression with one available tile argument. The splat operand
is an already evaluated scalar, represented by its `i32` bits. -/
inductive Expr where
  | input
  | makeRange (start : RangeStart)
  | splat (value : BitVec 32)

/-- Interpret `tt.make_range` as a dense logical tensor and `tt.splat` as a
Tensor splat. The dense elements are given directly, with no attribute codec. -/
def Expr.toTensor (expr : Expr) (input : Tile) : Tile :=
  match expr with
  | .input => input
  | .makeRange start =>
      Tensor.denseConstant (width := ⟨32, by decide⟩) fun i =>
        BitVec.ofNat 32 (start.val + i.1.val)
  | .splat value => Tensor.splat value

end Silmaril.MLIR.Triton

namespace Silmaril.MLIR.Gluon

/-- Rank-one `BlockedLayout([R], [32], [1], [0])` with one CTA and `R` equal
to 1 or 2. Both layouts use two slots per lane at extent 64. -/
inductive Layout where
  | sizePerThread1
  | sizePerThread2

/-- Abstract lane and register labels within the single warp. -/
structure Slot where
  lane : Fin 32
  reg : Fin 2

/-- With `R = 1`, the second register tile adds a stride of 32. With `R = 2`,
the two registers in each lane cover consecutive coordinates. -/
def Layout.slotToIndex (layout : Layout) (slot : Slot) : Fin 64 :=
  match layout with
  | .sizePerThread1 => ⟨slot.lane.val + 32 * slot.reg.val, by omega⟩
  | .sizePerThread2 => ⟨2 * slot.lane.val + slot.reg.val, by omega⟩

/-- Find the unique slot for a logical coordinate in the given layout. -/
def Layout.indexToSlot (layout : Layout) (index : Fin 64) : Slot :=
  match layout with
  | .sizePerThread1 => ⟨⟨index.val % 32, by omega⟩, ⟨index.val / 32, by omega⟩⟩
  | .sizePerThread2 => ⟨⟨index.val / 2, by omega⟩, ⟨index.val % 2, by omega⟩⟩

/-- A pure table of slot values with its layout tracked in the type. -/
structure Value (_layout : Layout) where
  atSlot : Slot → BitVec 32

/-- Read a logical tensor through the layout's coordinate-to-slot map. -/
def Value.toTensor {layout : Layout} (value : Value layout) : Triton.Tile :=
  fun i => value.atSlot (layout.indexToSlot i.1)

/-- `gl.convert_layout` with the default `assert_trivial = False`. Each
destination slot receives the source value at the same logical coordinate. -/
def Value.convertLayout {src : Layout} (value : Value src) (dst : Layout) : Value dst :=
  ⟨fun slot => value.atSlot (src.indexToSlot (dst.slotToIndex slot))⟩

/-- One available tile argument with layout `input`, and a tracked result layout. -/
inductive Expr (input : Layout) : Layout → Type where
  | arg : Expr input input
  | arange (layout : Layout) (start : Triton.RangeStart) : Expr input layout
  | full (layout : Layout) (value : BitVec 32) : Expr input layout
  | convertLayout {src : Layout} (dst : Layout) (expr : Expr input src) : Expr input dst

def Expr.denote {input layout : Layout} (expr : Expr input layout) (arg : Value input) :
    Value layout :=
  match expr with
  | .arg => arg
  | .arange layout start =>
      ⟨fun slot => BitVec.ofNat 32 (start.val + (layout.slotToIndex slot).val)⟩
  | .full _ value => ⟨fun _ => value⟩
  | .convertLayout dst expr => (expr.denote arg).convertLayout dst

/-- Erase layout annotations and conversions, keeping the corresponding
logical Triton expression. -/
def Expr.erase {input layout : Layout} : Expr input layout → Triton.Expr
  | .arg => .input
  | .arange _ start => .makeRange start
  | .full _ value => .splat value
  | .convertLayout _ expr => expr.erase

end Silmaril.MLIR.Gluon
