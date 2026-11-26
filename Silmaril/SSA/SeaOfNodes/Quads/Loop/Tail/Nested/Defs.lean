module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Defs

/-! # A checked nested split with one common three-occurrence merge -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested

open SeaOfNodes.Diamond (Model ValueSort dataPorts)
open RVSDG (Port)
open Join (Block)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}

/-- The outer true edge goes to the inner split. List incoming occurrences
in source traversal order: inner true, inner false, then outer false. -/
inductive Occurrence
  | innerTrue
  | innerFalse
  | outerFalse
  deriving DecidableEq, Repr

/-- The checked shape admits disjoint linear arms, including direct edges
to the merge. The merge jumps to the distinct tested latch. -/
structure Program (src : Source Op regs out size) (entry : Fin size) where
  header : Fin size
  inner : Fin size
  onInnerTrue : Fin size
  onInnerFalse : Fin size
  onOuterFalse : Fin size
  join : Fin size
  latch : Fin size
  outerTest : Port (dataPorts regs) (.value .predicate)
  innerTest : Port (dataPorts regs) (.value .predicate)
  again : Port (dataPorts regs) (.value .predicate)
  result : Port (dataPorts regs) (.value out)
  entryEdge : (src entry).terminator = .transfer (.jump header)
  outerEdge : (src header).terminator = .branch outerTest (.jump inner) (.jump onOuterFalse)
  innerEdge : (src inner).terminator = .branch innerTest (.jump onInnerTrue) (.jump onInnerFalse)
  innerTrue : Chain.Segment src join onInnerTrue
  innerFalse : Chain.Segment src join onInnerFalse
  outerFalse : Chain.Segment src join onOuterFalse
  joinEdge : (src join).terminator = .transfer (.jump latch)
  latchEdge : (src latch).terminator = .branch again (.jump header) (.ret result)
  innerDistinct : onInnerTrue ≠ onInnerFalse
  distinct : ([entry, header, inner] ++ innerTrue.blocks ++ innerFalse.blocks ++
    outerFalse.blocks ++ [join, latch]).Nodup
  covers : ([entry, header, inner] ++ innerTrue.blocks ++ innerFalse.blocks ++
    outerFalse.blocks ++ [join, latch]).length = size

/-- Discover the merge from the outer false route, then require both inner
routes to reach that same merge by following only checked jumps. -/
def check (src : Source Op regs out size) (entry : Fin size) : Option (Program src entry) :=
  match entryEdge : (src entry).terminator with
  | .transfer (.jump header) =>
    match outerEdge : (src header).terminator with
    | .branch outerTest (.jump inner) (.jump onOuterFalse) =>
      match innerEdge : (src inner).terminator with
      | .branch innerTest (.jump onInnerTrue) (.jump onInnerFalse) => do
        let outerRoute ← Chain.findPath src header size onOuterFalse
        let some join := outerRoute.beforeLatch | none
        let outerFalse ← outerRoute.segmentTo join
        let trueRoute ← Chain.findPath src header size onInnerTrue
        let falseRoute ← Chain.findPath src header size onInnerFalse
        let innerTrue ← trueRoute.segmentTo join
        let innerFalse ← falseRoute.segmentTo join
        match joinEdge : (src join).terminator with
        | .transfer (.jump latch) =>
          match latchEdge : (src latch).terminator with
          | .branch again (.jump target) (.ret result) =>
            let order := [entry, header, inner] ++ innerTrue.blocks ++ innerFalse.blocks ++
              outerFalse.blocks ++ [join, latch]
            if shape : target = header ∧ onInnerTrue ≠ onInnerFalse ∧ order.Nodup ∧ order.length = size then
              some ⟨header, inner, onInnerTrue, onInnerFalse, onOuterFalse, join, latch, outerTest, innerTest,
                again, result, entryEdge, outerEdge, innerEdge, innerTrue, innerFalse, outerFalse, joinEdge,
                shape.1 ▸ latchEdge, shape.2.1, shape.2.2.1, shape.2.2.2⟩
            else none
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)

def Program.armStart : Occurrence → Fin size
  | .innerTrue => p.onInnerTrue
  | .innerFalse => p.onInnerFalse
  | .outerFalse => p.onOuterFalse

def Program.arm (occurrence : Occurrence) : Chain.Segment src p.join (p.armStart occurrence) :=
  match occurrence with
  | .innerTrue => p.innerTrue
  | .innerFalse => p.innerFalse
  | .outerFalse => p.outerFalse

def Program.splitSite : Occurrence → Fin size
  | .innerTrue | .innerFalse => p.inner
  | .outerFalse => p.header

/-- Recover the original predecessor while retaining the occurrence that
identifies the route. A direct edge is owned by its split block. -/
def Program.predecessor (occurrence : Occurrence) : Fin size :=
  (p.arm occurrence).predecessor (p.splitSite occurrence)

/-- Collect exactly the executed source writes before this merge input.
The join's own writes are outside all three incoming scopes. -/
def Program.pathQuads (occurrence : Occurrence) : Block Op regs :=
  (src p.header).body ++
    match occurrence with
    | .innerTrue | .innerFalse => (src p.inner).body ++ (p.arm occurrence).quads
    | .outerFalse => (p.arm occurrence).quads

def Program.incomingTransfer (occurrence : Occurrence) :=
  CFG.compileBlock (p.pathQuads occurrence) (initial regs)

/-- Read all Φ arguments from the same occurrence's final version map. -/
def Program.mergeBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m)
    (occurrence : Occurrence) : Bank (regs := regs) m :=
  let compiled := p.incomingTransfer occurrence
  compiled.outgoing.read old (compiled.flow.eval m old PUnit.unit)

/-- Both decisions use their own post-block bank. -/
def Program.selected (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m) : Occurrence :=
  let outer := (src p.header).body.eval m old
  if (outer.get p.outerTest).down then
    let inner := (src p.inner).body.eval m outer
    if (inner.get p.innerTest).down then .innerTrue else .innerFalse
  else .outerFalse

/-- Count source visits from the header up to, but excluding, the merge. -/
def Program.mergeVisits : Occurrence → Nat
  | .innerTrue => p.innerTrue.blocks.length + 2
  | .innerFalse => p.innerFalse.blocks.length + 2
  | .outerFalse => p.outerFalse.blocks.length + 1

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested
