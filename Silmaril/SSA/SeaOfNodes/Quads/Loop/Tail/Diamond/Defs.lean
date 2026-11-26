module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Defs

/-! # A checked quad loop with one internal diamond -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond

open SeaOfNodes.Diamond (ValueSort Model Ty dataPorts)
open RVSDG (Dialect Port PortType Wires extend)
open RVSDG.NestedTheta (Term)
open Join (Block Opcode)
open Join.Finite (Stage Plan lastBank)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

abbrev Source (Op : SeaOfNodes.Diamond.Signature.{u, v} Data)
    (regs : List (ValueSort Data)) (out : ValueSort Data) := Tail.Source Op regs out 6

/-- The source has an entry, a data-dependent split at the header, two
predecessors of a merge, and a distinct tested latch after the merge. -/
structure Program (src : Source Op regs out) (entry : Fin 6) where
  header : Fin 6
  onTrue : Fin 6
  onFalse : Fin 6
  join : Fin 6
  latch : Fin 6
  condition : Port (dataPorts regs) (.value .predicate)
  again : Port (dataPorts regs) (.value .predicate)
  result : Port (dataPorts regs) (.value out)
  entryEdge : (src entry).terminator = .transfer (.jump header)
  splitEdge : (src header).terminator = .branch condition (.jump onTrue) (.jump onFalse)
  trueEdge : (src onTrue).terminator = .transfer (.jump join)
  falseEdge : (src onFalse).terminator = .transfer (.jump join)
  joinEdge : (src join).terminator = .transfer (.jump latch)
  latchEdge : (src latch).terminator = .branch again (.jump header) (.ret result)
  distinct : [entry, header, onTrue, onFalse, join, latch].Nodup

def check (src : Source Op regs out) (entry : Fin 6) : Option (Program src entry) :=
  match entryEdge : (src entry).terminator with
  | .transfer (.jump header) =>
    match splitEdge : (src header).terminator with
    | .branch condition (.jump onTrue) (.jump onFalse) =>
      match trueEdge : (src onTrue).terminator, falseEdge : (src onFalse).terminator with
      | .transfer (.jump join), .transfer (.jump otherJoin) =>
        if same : otherJoin = join then
          match joinEdge : (src join).terminator with
          | .transfer (.jump latch) =>
            match latchEdge : (src latch).terminator with
            | .branch again (.jump target) (.ret result) =>
              if shape : target = header ∧ [entry, header, onTrue, onFalse, join, latch].Nodup then
                some ⟨header, onTrue, onFalse, join, latch, condition, again, result, entryEdge,
                  splitEdge, trueEdge, same ▸ falseEdge, joinEdge, shape.1 ▸ latchEdge, shape.2⟩
              else none
            | _ => none
          | _ => none
        else none
      | _, _ => none
    | _ => none
  | _ => none

variable {src : Source Op regs out} {entry : Fin 6} (p : Program src entry)

/-- The merge columns are ordered by the header's true and false occurrences. -/
def Program.predecessor : Fin 2 → Fin 6 :=
  Fin.cases p.onTrue (fun _ => p.onFalse)

def Program.stage : Stage Op regs :=
  ⟨(src p.onTrue).body, (src p.onFalse).body, [], .test p.condition (.take 0) (.take 1)⟩

def Program.tail : Block Op regs := (src p.join).body ++ (src p.latch).body

/-- Run the source activation, including the selected arm and both blocks
after reconvergence. The resulting bank supplies feedback or the return. -/
def Program.nextBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m) : Bank (regs := regs) m :=
  p.tail.eval m (p.stage.eval m ((src p.header).body.eval m old))

section Prefix

variable {V S : Type u} {Φ : Dialect.{u, v} V S}
variable {args bank outs : List (PortType V S)} {suffix : List (List (PortType V S))}

/-- Use a base RVSDG region as a prefix of a nested one. The continuation
receives its actual result wires in their existing producer scope. -/
def thenBase : {past frontSigs : List (List (PortType V S))} →
    RVSDG.Term Φ args past frontSigs bank →
    (Wires args (extend past frontSigs) bank → Term Φ args (extend past frontSigs) suffix outs) →
    Term Φ args past (frontSigs ++ suffix) outs
  | _, _, .ret wires, next => next wires
  | _, _, .bind node children rest, next =>
    .bind (.ofBase node) (fun i => .ofBase (children i)) (thenBase rest next)

end Prefix

abbrev bodyPorts (regs : List (ValueSort Data)) :=
  RVSDG.Theta.BodyResults (dataPorts regs)

abbrev Program.plan : Plan Op regs := [p.stage]

abbrev Program.bodySigs :=
  (src p.header).body.producers ++ (p.plan.producers ++ (p.tail.producers ++ [bodyPorts regs]))

/-- Read the post-latch test and tag the entire updated bank for stop or feedback. -/
def Program.routeLatch {past : List (List (Ty Data))}
    (bank : Wires (dataPorts regs) past (dataPorts regs)) :
    Term (Opcode Op) (dataPorts regs) past [bodyPorts regs] (bodyPorts regs) :=
  let node : RVSDG.Node (Opcode Op) (dataPorts regs) past (bodyPorts regs) :=
    ⟨_, .simple (.route (.test p.again (.take 1) (.take 0))), bank, Fin.elim0⟩
  .bind (.ofBase node) (fun i => i.elim0) (.ret (lastBank past (bodyPorts regs)))

/-- The header compiles into the existing γ selector and arm regions. Their
result ports are the merge Φs. The join and latch read that same selected bank. -/
def Program.thetaBody :
    Term (Opcode Op) (dataPorts regs) [] p.bodySigs (bodyPorts regs) :=
  thenBase ((src p.header).body.lowerFrom (initial regs) .jump) fun current =>
    thenBase (p.plan.lowerFrom current) fun merged =>
      thenBase (p.tail.lowerFrom merged .jump) p.routeLatch

def Program.iterateThenReturn {past : List (List (Ty Data))}
    (bank : Wires (dataPorts regs) past (dataPorts regs)) :
    Term (Opcode Op) (dataPorts regs) past [dataPorts regs] [.value out] :=
  .bind ⟨_, .theta (dataPorts regs), bank, fun _ => p.bodySigs⟩
    (fun _ => p.thetaBody) (.ret (.cons ((lastBank past (dataPorts regs)).get p.result) .nil))

/-- The preheader supplies the entry bank. The numbered θ binds the feedback
bank atomically and returns the result slot of the stopping activation. -/
def Program.lowerTerm :
    Term (Opcode Op) (dataPorts regs) [] ((src entry).body.producers ++ [dataPorts regs]) [.value out] :=
  thenBase ((src entry).body.lowerFrom (initial regs) .jump) p.iterateThenReturn

def Program.lower :
    RVSDG.NestedTheta.Graph (Opcode Op) (dataPorts regs) []
      ((src entry).body.producers ++ [dataPorts regs]) [.value out] :=
  p.lowerTerm.toGraph

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond
