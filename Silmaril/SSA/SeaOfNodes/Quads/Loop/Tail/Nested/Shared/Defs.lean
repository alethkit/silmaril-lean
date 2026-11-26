module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Defs

/-! # Checked inner reconvergence before the outer merge -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared

open SeaOfNodes.Diamond (Model ValueSort)
open Join (Block)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}

/-- A factorization of both ordered routes at their first shared block. -/
structure CommonTail {target leftStart rightStart : Fin size}
    (left : Chain.Segment src target leftStart) (right : Chain.Segment src target rightStart) where
  meet : Fin size
  leftPrefix : Chain.Segment src meet leftStart
  rightPrefix : Chain.Segment src meet rightStart
  suffix : Chain.Segment src target meet
  nonempty : suffix.blocks ≠ []
  leftOrder : left.blocks = leftPrefix.blocks ++ suffix.blocks
  rightOrder : right.blocks = rightPrefix.blocks ++ suffix.blocks

/-- The independently checked prefixes must account for both original
routes in order with one and the same nonempty suffix. -/
def commonTail {target leftStart rightStart : Fin size}
    (left : Chain.Segment src target leftStart) (right : Chain.Segment src target rightStart) :
    Option (CommonTail left right) := do
  let some meet := left.blocks.find? right.blocks.contains | none
  let yes ← left.cutAt meet
  let no ← right.cutAt meet
  if same : yes.2.blocks ≠ [] ∧ left.blocks = yes.1.blocks ++ yes.2.blocks ∧
      right.blocks = no.1.blocks ++ yes.2.blocks then
    some ⟨meet, yes.1, no.1, yes.2, same.1, same.2.1, same.2.2⟩
  else none

/-- The block order accounts for the two split sites, their exclusive
prefixes, each shared suffix once, and the original join and latch. -/
structure Program (src : Source Op regs out size) (entry : Fin size) extends Control src entry where
  meet : Fin size
  outerMeet : Fin size
  innerTrue : Chain.Segment src meet onInnerTrue
  innerFalse : Chain.Segment src meet onInnerFalse
  suffix : Chain.Segment src outerMeet meet
  outerFalse : Chain.Segment src outerMeet onOuterFalse
  outerSuffix : Chain.Segment src join outerMeet
  nonempty : suffix.blocks ≠ []
  distinct : ([entry, header, inner] ++ innerTrue.blocks ++ innerFalse.blocks ++ suffix.blocks ++
    outerFalse.blocks ++ outerSuffix.blocks ++ [join, latch]).Nodup
  covers : ([entry, header, inner] ++ innerTrue.blocks ++ innerFalse.blocks ++ suffix.blocks ++
    outerFalse.blocks ++ outerSuffix.blocks ++ [join, latch]).length = size

/-- Validate the complete partition of the original table. A nonempty
inner suffix must still belong exclusively to the outer true route. -/
def Program.admitWithOuter (control : Control src entry) (meet outerMeet : Fin size)
    (innerTrue : Chain.Segment src meet control.onInnerTrue)
    (innerFalse : Chain.Segment src meet control.onInnerFalse)
    (suffix : Chain.Segment src outerMeet meet)
    (outerFalse : Chain.Segment src outerMeet control.onOuterFalse)
    (outerSuffix : Chain.Segment src control.join outerMeet) : Option (Program src entry) :=
  let order := [entry, control.header, control.inner] ++ innerTrue.blocks ++ innerFalse.blocks ++
    suffix.blocks ++ outerFalse.blocks ++ outerSuffix.blocks ++ [control.join, control.latch]
  if shape : suffix.blocks ≠ [] ∧ order.Nodup ∧ order.length = size then
    some ⟨control, meet, outerMeet, innerTrue, innerFalse, suffix, outerFalse, outerSuffix,
      shape.1, shape.2.1, shape.2.2⟩
  else none

/-- The original profile ends both outer routes at the final join. -/
def Program.admit (control : Control src entry) (meet : Fin size)
    (innerTrue : Chain.Segment src meet control.onInnerTrue)
    (innerFalse : Chain.Segment src meet control.onInnerFalse)
    (suffix : Chain.Segment src control.join meet)
    (outerFalse : Chain.Segment src control.join control.onOuterFalse) : Option (Program src entry) :=
  admitWithOuter control meet control.join innerTrue innerFalse suffix outerFalse .empty

/-- Admit inner reconvergence with a disjoint outer false route. -/
def check (src : Source Op regs out size) (entry : Fin size) : Option (Program src entry) := do
  let routes ← Nested.findRoutes src entry
  let inner ← commonTail routes.innerTrue routes.innerFalse
  Program.admit routes.toControl inner.meet inner.leftPrefix inner.rightPrefix inner.suffix routes.outerFalse

/-- When both outer routes have an ordered common tail before the final
join, cut it after the inner reconvergence and include it exactly once. -/
def checkOuter (src : Source Op regs out size) (entry : Fin size) : Option (Program src entry) := do
  let routes ← Nested.findRoutes src entry
  let inner ← commonTail routes.innerTrue routes.innerFalse
  let outer ← commonTail inner.suffix routes.outerFalse
  Program.admitWithOuter routes.toControl inner.meet outer.meet inner.leftPrefix inner.rightPrefix
    outer.leftPrefix outer.rightPrefix outer.suffix

variable (p : Program src entry)

def Program.blockOrder : List (Fin size) :=
  [entry, p.header, p.inner] ++ p.innerTrue.blocks ++ p.innerFalse.blocks ++ p.suffix.blocks ++
    p.outerFalse.blocks ++ p.outerSuffix.blocks ++ [p.join, p.latch]

/-- The predecessor and outgoing slot at the inner reconvergence. The
final jump of a nonempty prefix occupies slot zero. -/
def Program.innerEdgeOccurrence (taken : Bool) : Fin size × Fin 2 :=
  match taken with
  | true => (p.innerTrue.predecessor p.inner, 0)
  | false => (p.innerFalse.predecessor p.inner, bif p.innerFalse.blocks.isEmpty then 1 else 0)

/-- The outer true predecessor finishes the exclusive inner suffix.
The outer false route can enter directly from the header's false slot. -/
def Program.outerEdgeOccurrence (taken : Bool) : Fin size × Fin 2 :=
  match taken with
  | true => (p.suffix.predecessor p.inner, 0)
  | false => (p.outerFalse.predecessor p.header, bif p.outerFalse.blocks.isEmpty then 1 else 0)

def Program.prefixTarget : Occurrence → Fin size
  | .innerTrue | .innerFalse => p.meet
  | .outerFalse => p.outerMeet

def Program.prefixQuads (occurrence : Occurrence) : Block Op regs :=
  (src p.header).body ++ match occurrence with
  | .innerTrue => (src p.inner).body ++ p.innerTrue.quads
  | .innerFalse => (src p.inner).body ++ p.innerFalse.quads
  | .outerFalse => p.outerFalse.quads

/-- Each prefix supplies its independently compiled latest definitions. -/
def Program.prefixTransfer (occurrence : Occurrence) :=
  CFG.compileBlock (p.prefixQuads occurrence) (initial regs)

/-- The shared segment takes a single full typed bank at the reconvergence. -/
def Program.suffixTransfer :=
  CFG.compileBlock p.suffix.quads (initial regs)

/-- The common outer tail takes the selected outer γ bank as its input. -/
def Program.outerSuffixTransfer :=
  CFG.compileBlock p.outerSuffix.quads (initial regs)

def Program.prefixBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m)
    (occurrence : Occurrence) : Bank (regs := regs) m :=
  let compiled := p.prefixTransfer occurrence
  compiled.outgoing.read old (compiled.flow.eval m old PUnit.unit)

def Program.suffixBank (m : Model.{u, v, w} Op) (incoming : Bank (regs := regs) m) : Bank (regs := regs) m :=
  let compiled := p.suffixTransfer
  compiled.outgoing.read incoming (compiled.flow.eval m incoming PUnit.unit)

def Program.outerBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m)
    (occurrence : Occurrence) : Bank (regs := regs) m :=
  let incoming := p.prefixBank m old occurrence
  match occurrence with
  | .innerTrue | .innerFalse => p.suffixBank m incoming
  | .outerFalse => incoming

def Program.outerSuffixBank (m : Model.{u, v, w} Op) (incoming : Bank (regs := regs) m) :
    Bank (regs := regs) m :=
  let compiled := p.outerSuffixTransfer
  compiled.outgoing.read incoming (compiled.flow.eval m incoming PUnit.unit)

def Program.mergeBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m)
    (occurrence : Occurrence) : Bank (regs := regs) m :=
  p.outerSuffixBank m (p.outerBank m old occurrence)

def Program.prefixVisits : Occurrence → Nat
  | .innerTrue => p.innerTrue.blocks.length + 2
  | .innerFalse => p.innerFalse.blocks.length + 2
  | .outerFalse => p.outerFalse.blocks.length + 1

def Program.outerVisits (occurrence : Occurrence) : Nat :=
  p.prefixVisits occurrence + match occurrence with
    | .innerTrue | .innerFalse => p.suffix.blocks.length
    | .outerFalse => 0

def Program.mergeVisits (occurrence : Occurrence) : Nat :=
  p.outerVisits occurrence + p.outerSuffix.blocks.length

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared
