module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Defs

/-! # Checked finite chains of quad blocks in one loop activation -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain

open Diamond (Ty ValueSort dataPorts)
open RVSDG (Port Wires extend)
open Join (Block)
open SeaOfNodes.Loop (Graph Incoming headerPorts)

universe u v

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {header site : Fin size}

/-- The checked source edges of one activation. The terminal constructor
records exactly the true feedback arm and the false return arm. -/
inductive Path (src : Source Op regs out size) (header : Fin size) : Fin size → Type u
  | latch (site : Fin size) (test : Port (dataPorts regs) (.value .predicate))
      (result : Port (dataPorts regs) (.value out))
      (edge : (src site).terminator = .branch test (.jump header) (.ret result)) :
      Path src header site
  | jump (site : Fin size) {next : Fin size}
      (edge : (src site).terminator = .transfer (.jump next)) (rest : Path src header next) :
      Path src header site

def Path.blocks : {site : Fin size} → Path src header site → List (Fin size)
  | _, .latch site .. => [site]
  | _, .jump site _ rest => site :: rest.blocks

def Path.latchBlock : {site : Fin size} → Path src header site → Fin size
  | _, .latch site .. => site
  | _, .jump _ _ rest => rest.latchBlock

def Path.test : {site : Fin size} → Path src header site → Port (dataPorts regs) (.value .predicate)
  | _, .latch _ test _ _ => test
  | _, .jump _ _ rest => rest.test

def Path.result : {site : Fin size} → Path src header site → Port (dataPorts regs) (.value out)
  | _, .latch _ _ result _ => result
  | _, .jump _ _ rest => rest.result

def Path.quads : {site : Fin size} → Path src header site → Block Op regs
  | _, .latch site .. => (src site).body
  | _, .jump site _ rest => (src site).body ++ rest.quads

/-- Follow actual source jumps. Running out of blocks, branching early, or
ending with any other pair of latch arms fails the check. -/
def findPath (src : Source Op regs out size) (header : Fin size) :
    Nat → (site : Fin size) → Option (Path src header site)
  | 0, _ => none
  | fuel + 1, site =>
    match edge : (src site).terminator with
    | .transfer (.jump next) => (findPath src header fuel next).map (.jump site edge)
    | .branch test (.jump target) (.ret result) =>
      if same : target = header then
        some (.latch site test result (same ▸ edge))
      else none
    | _ => none

/-- The entry followed by the checked activation accounts for every original
block exactly once. The latch may be the header in a one-block activation. -/
structure Program (src : Source Op regs out size) (entry : Fin size) where
  header : Fin size
  entryJump : (src entry).terminator = .transfer (.jump header)
  activation : Path src header header
  distinct : (entry :: activation.blocks).Nodup
  covers : (entry :: activation.blocks).length = size

def check (src : Source Op regs out size) (entry : Fin size) : Option (Program src entry) :=
  match jump : (src entry).terminator with
  | .transfer (.jump header) => do
    let path ← findPath src header (size - 1) header
    if shape : (entry :: path.blocks).Nodup ∧ (entry :: path.blocks).length = size then
      some ⟨header, jump, path, shape.1, shape.2⟩
    else none
  | _ => none

variable {entry : Fin size} (p : Program src entry)

def Program.blockOrder : List (Fin size) := entry :: p.activation.blocks

def Program.activationLength : Nat := p.activation.blocks.length

/-- Both columns target the header. Entry is the preheader's jump and
feedback is the true occurrence of the recorded latch. -/
def Program.predecessor : Incoming → Fin size
  | .entry => entry
  | .backedge => p.activation.latchBlock

/-- Recompute the reaching map one original block at a time, passing a
jump's outgoing origins straight to its successor. -/
def Path.outgoing {args : List (Ty Data)} :
    {site : Fin size} → (path : Path src header site) → {past : List (List (Ty Data))} →
    Wires args past (dataPorts regs) → Wires args (extend past path.quads.producers) (dataPorts regs)
  | _, .latch site .., _, current => (CFG.compileBlock (src site).body current).outgoing
  | _, .jump site _ rest, past, current =>
    let next := (CFG.compileBlock (src site).body current).outgoing
    cast (congrArg (fun ctx => Wires args ctx (dataPorts regs))
      (append_context (src site).body rest.quads past).symm) (rest.outgoing next)

/-- The native producer table schedules the forced chain in source order. -/
def Program.fuse : Blocks.Program Op regs out :=
  ⟨.jump (src entry).body, .branch p.activation.quads p.activation.test p.activation.result⟩

def Program.lower :
    Graph Op regs regs (src entry).body.producers p.activation.quads.producers out :=
  p.fuse.lower

/-- The feedback column starts with the pending typed header arguments. -/
def Program.feedbackColumn :
    Wires (headerPorts regs regs) (extend [] p.activation.quads.producers) (dataPorts regs) :=
  p.activation.outgoing (headerVersions regs)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain
