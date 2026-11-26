module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Defs

/-! # Prune the θ interface of a checked quad diamond -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune

open SeaOfNodes.Diamond (Dataflow Model Ty Val ValueSort dataPorts)
open RVSDG (Port Tuple Wires extend)
open RVSDG.NestedTheta (Term)
open Join (Opcode)
open Join.Finite (lastBank)
open Blocks (Bank)
open Blocks.Prune (Mask readSchedule renameFlow renameWires)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry)

def headerTransfer :=
  CFG.compileBlock (src p.header).body (initial regs)

/-- All header producer reads and the complete post-header bank are roots.
The return slot stays in the stop packet as well as in the carrier. -/
def carriedMask : Mask regs :=
  let flow := headerTransfer p
  let reads := readSchedule flow.flow ++ [flow.outgoing.addresses]
  let live := RVSDG.NestedTheta.Liveness.sweep reads 0
  Mask.ofSlots (fun i => i == p.result.index || live.contains (.arg i)) regs

/-- A smaller entry bank is safe only if it can reconstitute every
post-header field without reading a dropped value. All later γ operands,
latch and return tests, and feedback wires then see the original values. -/
structure Checked (p : Program src entry) (mask : Mask regs) where
  flow : Dataflow Op (dataPorts mask.kept) [] (src p.header).body.producers
  outgoing : Wires (dataPorts mask.kept) (extend [] (src p.header).body.producers) (dataPorts regs)
  result : Port (dataPorts mask.kept) (.value out)
  smaller : mask.kept.length < regs.length
  flow_eq : renameFlow mask.rename (headerTransfer p).flow = some flow
  outgoing_eq : renameWires mask.rename (headerTransfer p).outgoing = some outgoing
  result_eq : mask.rename p.result = some result

def checkMask (mask : Mask regs) : Option (Checked p mask) :=
  if smaller : mask.kept.length < regs.length then
    match flow_eq : renameFlow mask.rename (headerTransfer p).flow,
          outgoing_eq : renameWires mask.rename (headerTransfer p).outgoing,
          result_eq : mask.rename p.result with
    | some flow, some outgoing, some result =>
      some ⟨flow, outgoing, result, smaller, flow_eq, outgoing_eq, result_eq⟩
    | _, _, _ => none
  else none

def prune : Option (Checked p (carriedMask p)) := checkMask p (carriedMask p)

variable {p} {mask : Mask regs} (checked : Checked p mask)

def Checked.headerBank (m : Model.{u, v, w} Op) (old : Bank (regs := mask.kept) m) :
    Bank (regs := regs) m :=
  checked.outgoing.read old (checked.flow.eval m old PUnit.unit)

/-- Use the same trace observer and source arm order as the full bank. -/
def Checked.trace (m : Model.{u, v, w} Op) : Nat → Bank (regs := mask.kept) m → List (Fin 2) :=
  traceFrom fun old =>
    let header := checked.headerBank m old
    let next := p.tail.eval m (p.stage.eval m header)
    (p.stage.choice.eval header, (next.get p.again).down, mask.project next)

/-- Emit the validated producer table as an ordinary base RVSDG prefix. -/
def lowerFlow {args results : List (Ty Data)} :
    {past sigs : List (List (Ty Data))} → Dataflow Op args past sigs →
    Wires args (extend past sigs) results → RVSDG.Term (Opcode Op) args past sigs results
  | _, _, .nil, result => .ret result
  | _, _, .cons op operands rest, result =>
    .bind ⟨_, .simple (.pure op), operands, Fin.elim0⟩ (fun i => i.elim0) (lowerFlow rest result)

def projectPacket (mask : Mask regs) {F : Ty Data → Type w} :
    Tuple F (bodyPorts regs) → Tuple F (bodyPorts mask.kept)
  | .cons tag bank => .cons tag (mask.project bank)

def routeProjected (p : Program src entry) (mask : Mask regs) {args : List (Ty Data)}
    {past : List (List (Ty Data))} (bank : Wires args past (dataPorts regs)) :
    Term (Opcode Op) args past [bodyPorts regs] (bodyPorts mask.kept) :=
  .bind (.ofBase (p.latchNode bank)) (fun i => i.elim0)
    (.ret (projectPacket mask (lastBank past (bodyPorts regs))))

/-- The smaller θ argument bank is expanded by the header producers.
The γ regions and their selected merge column are reused verbatim. -/
def Checked.thetaBody :
    Term (Opcode Op) (dataPorts mask.kept) [] p.bodySigs (bodyPorts mask.kept) :=
  thenBase (lowerFlow checked.flow checked.outgoing) fun current =>
    p.afterHeader current (routeProjected p mask)

def Checked.iterateThenReturn {past : List (List (Ty Data))}
    (bank : Wires (dataPorts regs) past (dataPorts regs)) :
    Term (Opcode Op) (dataPorts regs) past [dataPorts mask.kept] [.value out] :=
  .bind ⟨_, .theta (dataPorts mask.kept), mask.project bank, fun _ => p.bodySigs⟩
    (fun _ => checked.thetaBody)
    (.ret (.cons ((lastBank past (dataPorts mask.kept)).get checked.result) .nil))

def Checked.lowerTerm :
    Term (Opcode Op) (dataPorts regs) [] ((src entry).body.producers ++ [dataPorts mask.kept]) [.value out] :=
  thenBase ((src entry).body.lowerFrom (initial regs) .jump) checked.iterateThenReturn

def Checked.lower :
    RVSDG.NestedTheta.Graph (Opcode Op) (dataPorts regs) []
      ((src entry).body.producers ++ [dataPorts mask.kept]) [.value out] :=
  checked.lowerTerm.toGraph

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune
