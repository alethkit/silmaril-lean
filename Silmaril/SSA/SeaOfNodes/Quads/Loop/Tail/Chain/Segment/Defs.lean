module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Defs

/-! # A nonempty checked jump segment ending just before a given block -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain

open Diamond (ValueSort Signature)
open Join (Block)

universe u v

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {target site header : Fin size}

/-- The body of the destination block is outside this segment. -/
inductive Segment (src : Source Op regs out size) (target : Fin size) : Fin size → Type u
  | last (site : Fin size) (edge : (src site).terminator = .transfer (.jump target)) :
      Segment src target site
  | jump (site : Fin size) {next : Fin size}
      (edge : (src site).terminator = .transfer (.jump next)) (rest : Segment src target next) :
      Segment src target site

def Segment.blocks : {site : Fin size} → Segment src target site → List (Fin size)
  | _, .last site _ => [site]
  | _, .jump site _ rest => site :: rest.blocks

def Segment.lastBlock : {site : Fin size} → Segment src target site → Fin size
  | _, .last site _ => site
  | _, .jump _ _ rest => rest.lastBlock

def Segment.quads : {site : Fin size} → Segment src target site → Block Op regs
  | _, .last site _ => (src site).body
  | _, .jump site _ rest => (src site).body ++ rest.quads

/-- Cut a checked jump chain at a transfer to the requested destination. -/
def Path.segmentTo (target : Fin size) :
    {site : Fin size} → Path src header site → Option (Segment src target site)
  | _, .latch .. => none
  | _, .jump site (next := next) edge rest =>
    if ends : next = target then some (.last site (ends ▸ edge))
    else (rest.segmentTo target).map (.jump site edge)

/-- Locate the block immediately before the tested latch on a checked path. -/
def Path.beforeLatch : {site : Fin size} → Path src header site → Option (Fin size)
  | _, .latch .. => none
  | _, .jump site _ rest => rest.beforeLatch.or (some site)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain
