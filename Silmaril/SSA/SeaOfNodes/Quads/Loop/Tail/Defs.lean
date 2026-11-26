module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Defs

/-! # Three-block, tail-tested quad source loops -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail

open Diamond (Model Ty ValueSort dataPorts sortValue)
open RVSDG (Port Wires extend)
open Join (Block)
open Blocks (Bank)
open SeaOfNodes.Loop (Graph headerPorts)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

inductive Destination (regs : List (ValueSort Data)) (out : ValueSort Data) where
  | jump (block : Fin 3)
  | ret (result : Port (dataPorts regs) (.value out))

inductive Terminator (regs : List (ValueSort Data)) (out : ValueSort Data) where
  | transfer (destination : Destination regs out)
  | branch (test : Port (dataPorts regs) (.value .predicate))
      (onTrue onFalse : Destination regs out)

def Terminator.select (m : Model.{u, v, w} Op) (bank : Bank (regs := regs) m) :
    Terminator regs out → Destination regs out
  | .transfer dest => dest
  | .branch test onTrue onFalse => if (bank.get test).down then onTrue else onFalse

structure SourceBlock (Op : Diamond.Signature.{u, v} Data) (regs : List (ValueSort Data))
    (out : ValueSort Data) where
  body : Block Op regs
  terminator : Terminator regs out

/-- A source table can express edges outside the admitted single-loop shape. -/
abbrev Source (Op : Diamond.Signature.{u, v} Data) (regs : List (ValueSort Data))
    (out : ValueSort Data) := Fin 3 → SourceBlock Op regs out

/-- Execute one source block per fuel unit, including entry and the returning
latch. The branch reads the register bank after the block's assignments. -/
def Source.runFrom (src : Source Op regs out) (m : Model.{u, v, w} Op) :
    Nat → Fin 3 → Bank (regs := regs) m → Option (sortValue m.value out)
  | 0, _, _ => none
  | fuel + 1, index, bank =>
    let block := src index
    let next := block.body.eval m bank
    match block.terminator.select m next with
    | .jump target => runFrom src m fuel target next
    | .ret result => some (next.get result)

def Source.run (src : Source Op regs out) (m : Model.{u, v, w} Op) (fuel : Nat)
    (input : Bank (regs := regs) m) : Option (sortValue m.value out) :=
  src.runFrom m fuel 0 input

/-- Entry jumps to the header, the header jumps to the latch, and the latch
branches back to the header on true or returns a register on false. -/
structure Program (Op : Diamond.Signature.{u, v} Data) (regs : List (ValueSort Data))
    (out : ValueSort Data) where
  entry : Block Op regs
  header : Block Op regs
  latch : Blocks.Header Op regs out

def Program.source (p : Program Op regs out) : Source Op regs out :=
  fun i =>
    if i = 0 then ⟨p.entry, .transfer (.jump 1)⟩
    else if i = 1 then ⟨p.header, .transfer (.jump 2)⟩
    else ⟨p.latch.body, .branch p.latch.test (.jump 1) (.ret p.latch.result)⟩

/-- Admit exactly the three-block layout, with the entry at zero. -/
def Source.check (src : Source Op regs out) : Option (Program Op regs out) :=
  match (src 0).terminator, (src 1).terminator, (src 2).terminator with
  | .transfer (.jump toHeader), .transfer (.jump toLatch), .branch test (.jump feedback) (.ret result) =>
    if toHeader = 1 ∧ toLatch = 2 ∧ feedback = 1 then
      some ⟨(src 0).body, (src 1).body, .branch (src 2).body test result⟩
    else none
  | _, _, _ => none

/-- A pure activation crosses the header's unique outgoing jump before
reaching the latch test. Schedule both blocks into that activation. -/
def Program.fuse (p : Program Op regs out) : Blocks.Program Op regs out :=
  ⟨.jump p.entry, .branch (p.header ++ p.latch.body) p.latch.test p.latch.result⟩

variable (p : Program Op regs out)

/-- Allocate the pending loop-header definitions before compiling any quads. -/
def Program.headerTransfer :
    Loop.Transfer Op regs (headerPorts regs regs) [] p.header.producers :=
  CFG.compileBlock p.header (headerVersions regs)

/-- Latch-local operands read the header jump's computed reaching versions,
with the header producers already numbered in their native context. -/
def Program.latchTransfer :
    Loop.Transfer Op regs (headerPorts regs regs)
      (extend [] p.header.producers) p.latch.body.producers :=
  CFG.compileBlock p.latch.body p.headerTransfer.outgoing

/-- Numbering a concatenation extends the producer context in the same order. -/
theorem append_context (first second : Block Op regs) (past : List (List (Ty Data))) :
    extend past (first ++ second).producers = extend (extend past first.producers) second.producers := by
  induction first generalizing past with
  | nil => rfl
  | cons _ _ ih => exact ih _

/-- Place the latch's outgoing column in the fused activation's producer
context. The transport leaves every argument and producer index intact. -/
def Program.feedbackColumn :
    Wires (headerPorts regs regs) (extend [] (p.header ++ p.latch.body).producers) (dataPorts regs) :=
  cast (congrArg (fun context => Wires (headerPorts regs regs) context (dataPorts regs))
    (append_context p.header p.latch.body []).symm) p.latchTransfer.outgoing

/-- Keep the entry occurrence distinct and use the post-latch versions for
the feedback occurrence. The existing loop graph represents each fused activation. -/
def Program.lower : Graph Op regs regs p.entry.producers (p.header ++ p.latch.body).producers out :=
  p.fuse.lower

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail
