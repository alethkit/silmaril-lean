module

public import Silmaril.SSA.SeaOfNodes.Quads.CFG.Defs

/-! # Source construction of a quad loop with an explicit preheader -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks

open RVSDG (Port Tuple)
open Diamond (ValueSort Model Val dataPorts sortValue)
open Join (Block)
open SeaOfNodes.Loop (Graph Incoming appendTuple headerPorts)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

/-- Ordered assignments followed by the unconditional jump to the header. -/
structure Preheader (Op : Diamond.Signature.{u, v} Data) (regs : List (ValueSort Data)) where
  jump ::
  body : Block Op regs

/-- Ordered assignments followed by one conditional. True follows the
syntactic backedge to this header. False returns the specified register. -/
structure Header (Op : Diamond.Signature.{u, v} Data) (regs : List (ValueSort Data))
    (out : ValueSort Data) where
  branch ::
  body : Block Op regs
  test : Port (dataPorts regs) (.value .predicate)
  result : Port (dataPorts regs) (.value out)

structure Program (Op : Diamond.Signature.{u, v} Data) (regs : List (ValueSort Data))
    (out : ValueSort Data) where
  preheader : Preheader Op regs
  header : Header Op regs out

abbrev Bank (m : Model.{u, v, w} Op) := Tuple (Val m.value) (dataPorts regs)

variable (p : Program Op regs out) (m : Model.{u, v, w} Op)

/-- The jump sends the updated preheader bank, once per execution. -/
def Program.initial (input : Bank (regs := regs) m) : Bank (regs := regs) m :=
  p.preheader.body.eval m input

/-- Both terminator operands read the bank after all header assignments. -/
def Program.step (old : Bank (regs := regs) m) :
    sortValue m.value out ⊕ Bank (regs := regs) m :=
  let next := p.header.body.eval m old
  if (next.get p.header.test).down then .inr next else .inl (next.get p.header.result)

def Program.evalFrom : Nat → Bank (regs := regs) m → Option (sortValue m.value out)
  | 0, old => match p.step m old with
    | .inl result => some result
    | .inr _ => none
  | budget + 1, old => match p.step m old with
    | .inl result => some result
    | .inr next => evalFrom budget next

def Program.evalBackedges (budget : Nat) (input : Bank (regs := regs) m) :
    Option (sortValue m.value out) :=
  p.evalFrom m budget (p.initial m input)

def Program.entryTransfer :
    Transfer Op regs (dataPorts regs) [] p.preheader.body.producers :=
  CFG.compileBlock p.preheader.body (Quads.initial regs)

/-- Allocate the pending header definitions before any header assignment is
translated. Header operands can read these ports while feedback is pending. -/
def Program.headerTransfer :
    Transfer Op regs (headerPorts regs regs) [] p.header.body.producers :=
  CFG.compileBlock p.header.body (headerVersions regs)

/-- Resolve the two occurrences from the independently computed outgoing
versions. Only now is the backedge column available. -/
def Program.lower : Graph Op regs regs p.preheader.body.producers p.header.body.producers out where
  preheader := p.entryTransfer.flow
  header := p.headerTransfer.flow
  phiInputs
    | .entry => p.entryTransfer.outgoing
    | .backedge => p.headerTransfer.outgoing
  predicate := p.headerTransfer.outgoing.get p.header.test
  result := p.headerTransfer.outgoing.get p.header.result

/-- Latch just the named occurrence, from its own immutable snapshot. The
backedge snapshot uses the old latch for every header read. -/
def Program.latch (edge : Incoming) (input old : Bank (regs := regs) m) : Bank (regs := regs) m :=
  match edge with
  | .entry => p.lower.initial m input
  | .backedge =>
    let args := appendTuple old input
    p.lower.latch m .backedge args (p.lower.header.eval m args PUnit.unit)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks
