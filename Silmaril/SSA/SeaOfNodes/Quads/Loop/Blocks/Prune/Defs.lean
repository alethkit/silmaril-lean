module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Defs

/-! # Conservative Phi pruning for a two-block quad loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune

open RVSDG (Address Origin Port Tuple Wires)
open Diamond (Dataflow Ty ValueSort dataPorts)
open SeaOfNodes.Loop (Graph headerPorts)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

/-- An ordered selection of carried fields, independent of their values. -/
inductive Mask : List (ValueSort Data) → Type u
  | nil : Mask []
  | keep {s rest} : Mask rest → Mask (s :: rest)
  | drop {s rest} : Mask rest → Mask (s :: rest)

def Mask.ofSlots (keepSlot : Nat → Bool) : (regs : List (ValueSort Data)) → Mask regs
  | [] => .nil
  | _ :: rest =>
    let tail := ofSlots (fun k => keepSlot (k + 1)) rest
    if keepSlot 0 then .keep tail else .drop tail

def Mask.kept : {regs : List (ValueSort Data)} → Mask regs → List (ValueSort Data)
  | _, .nil => []
  | _, .keep (s := s) tail => s :: tail.kept
  | _, .drop tail => tail.kept

/-- Project values or wires in register order. -/
def Mask.project {F : Ty Data → Type w} : {regs : List (ValueSort Data)} →
    (mask : Mask regs) → Tuple F (dataPorts regs) → Tuple F (dataPorts mask.kept)
  | _, .nil, .nil => .nil
  | _, .keep tail, .cons value rest => .cons value (tail.project rest)
  | _, .drop tail, .cons _ rest => tail.project rest

/-- A dropped position has no operand in the new carried bank. -/
def Mask.rename : {regs : List (ValueSort Data)} → (mask : Mask regs) →
    {t : Ty Data} → Port (dataPorts regs) t → Option (Port (dataPorts mask.kept) t)
  | _, .nil, _, port => nomatch port
  | _, .keep _, _, .head => some .head
  | _, .keep tail, _, .tail port => (tail.rename port).map Port.tail
  | _, .drop _, _, .head => none
  | _, .drop tail, _, .tail port => tail.rename port

abbrev Rename {T : Type u} (args target : List T) :=
  ∀ {t}, Port args t → Option (Port target t)

/-- Leave the fixed input segment of the header in scope. -/
def keepPrefix {T : Type u} {args target : List T} (rename : Rename args target) :
    (fixed : List T) → Rename (fixed ++ args) (fixed ++ target)
  | [], _, p => rename p
  | _ :: _, _, .head => some .head
  | _ :: rest, _, .tail p => (keepPrefix rename rest p).map Port.tail

def renameOrigin {args target : List (Ty Data)} {past : List (List (Ty Data))}
    (rename : Rename args target) {t : Ty Data} :
    Origin args past t → Option (Origin target past t)
  | .arg p => (rename p).map Origin.arg
  | .output i p => some (.output i p)

def renameWires {args target : List (Ty Data)} {past : List (List (Ty Data))}
    (rename : Rename args target) : {outs : List (Ty Data)} →
    Wires args past outs → Option (Wires target past outs)
  | _, .nil => some .nil
  | _, .cons wire rest =>
    match renameOrigin rename wire, renameWires rename rest with
    | some wire', some rest' => some (.cons wire' rest')
    | _, _ => none

def renameFlow {args target : List (Ty Data)} (rename : Rename args target) :
    {past sigs : List (List (Ty Data))} →
    Dataflow Op args past sigs → Option (Dataflow Op target past sigs)
  | _, _, .nil => some .nil
  | _, _, .cons op wires rest =>
    match renameWires rename wires, renameFlow rename rest with
    | some wires', some rest' => some (.cons op wires' rest')
    | _, _ => none

/-- The shared backward sweep reads every scheduled operation in order.
The pass retains every compiled producer. -/
def readSchedule {args : List (Ty Data)} :
    {past sigs : List (List (Ty Data))} → Dataflow Op args past sigs → List (List Address)
  | _, _, .nil => []
  | _, _, .cons _ wires rest => wires.addresses :: readSchedule rest

/-- The fully resolved header wires identify old-bank reads. A use after
a local write names that numbered producer instead of a carried argument. -/
def carriedMask (p : Program Op regs out) : Mask regs :=
  let graph := p.lower
  let reads := readSchedule graph.header ++ [[graph.predicate.address, graph.result.address]]
  let live := RVSDG.NestedTheta.Liveness.sweep reads 0
  Mask.ofSlots (fun k => live.contains (.arg ((dataPorts regs).length + k))) regs

abbrev PrunedGraph (p : Program Op regs out) (mask : Mask regs) :=
  Graph Op regs mask.kept p.preheader.body.producers p.header.body.producers out

/-- Validate a strict projection against every producer operand, the test
and return, and the retained feedback outputs. The producer order is kept. -/
def pruneWith (p : Program Op regs out) (mask : Mask regs) : Option (PrunedGraph p mask) :=
  if mask.kept.length < regs.length then
    let full := p.lower
    let rename : Rename (headerPorts regs regs) (headerPorts regs mask.kept) :=
      keepPrefix mask.rename (dataPorts regs)
    match renameFlow rename full.header, renameWires rename (mask.project (full.phiInputs .backedge)),
        renameOrigin rename full.predicate, renameOrigin rename full.result with
    | some header, some feedback, some test, some result =>
      some
        { preheader := full.preheader
          header := header
          phiInputs
            | .entry => mask.project (full.phiInputs .entry)
            | .backedge => feedback
          predicate := test
          result := result }
    | _, _, _, _ => none
  else none

/-- Derive the candidate from the source program and validate its typed wiring. -/
def prune (p : Program Op regs out) : Option (PrunedGraph p (carriedMask p)) :=
  pruneWith p (carriedMask p)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune
