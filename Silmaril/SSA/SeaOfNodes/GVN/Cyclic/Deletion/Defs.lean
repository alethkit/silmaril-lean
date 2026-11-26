module

public import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Defs

/-!
# Delete one unused producer from a pure loop header

The deleted result has no route. The suffix is rebuilt by traversing each
surviving ordered operand tuple with a partial typed route. The same route
must also handle the guard, all feedback operands, and the result.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion

open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts)
open RVSDG (Locals Origin Tuple Wires extend)
open Elimination (splitOrigin)

universe u v w

section Scope

variable {T : Type u} {args : List T} {past target : List (List T)} {t : T}

/-- In a deletion route, a missing result signifies a use of the deleted producer. -/
abbrev Route (args : List T) (past target : List (List T)) :=
  ∀ {t : T}, Origin args past t → Option (Origin args target t)

/-- Keep a binding and extend the partial route to its result. -/
def Route.push (route : Route args past target) (head : List T) :
    Route args (past ++ [head]) (target ++ [head]) :=
  fun wire => match splitOrigin head wire with
    | .inl prior => (route prior).map (weaken head)
    | .inr port => some (newest port)

/-- Traverse every occurrence in order, failing at an unroutable wire. -/
def Route.wires? (route : Route args past target) : {ports : List T} →
    Wires args past ports → Option (Wires args target ports)
  | _, .nil => some .nil
  | _, .cons wire tail => do
    let mapped ← route wire
    let rest ← route.wires? tail
    pure (.cons mapped rest)

/-- Forget the binding while retaining the routes for its prefix. -/
def drop (head : List T) : Route args (past ++ [head]) past :=
  fun wire => match splitOrigin head wire with
    | .inl prior => some prior
    | .inr _ => none

end Scope

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past target sigs : List (List (Ty Data))}
variable {out : ValueSort Data}

/-- Agreement is required at every old wire for which the partial route succeeds. -/
def Route.Agrees (route : Route args past target) (m : Model.{u,v,w} Op)
    (entry : Tuple (Val m.value) args) (old : Locals (Val m.value) past)
    (new : Locals (Val m.value) target) : Prop :=
  ∀ {t : Ty Data} (wire : Origin args past t) (mapped : Origin args target t),
    route wire = some mapped → Diamond.read m wire entry old = Diamond.read m mapped entry new

/-- Reindex each surviving header operand before appending its binding. -/
def routeSuffix? :
    {past sigs target : List (List (Ty Data))} → Dataflow Op args past sigs →
      Route args past target → Option (Dataflow Op args target sigs ×
        Route args (extend past sigs) (extend target sigs))
  | _, _, _, .nil, route => some (.nil, route)
  | _, _, _, .cons (out := out) opcode operands rest, route =>
    (route.wires? operands).bind fun mapped =>
      (routeSuffix? rest (route.push [.value out])).map fun (suffix, finalRoute) =>
        (.cons opcode mapped suffix, finalRoute)

structure Erasure (Op : Signature.{u,v} Data) (args : List (Ty Data))
    (past sigs : List (List (Ty Data))) where
  sigs' : List (List (Ty Data))
  flow : Dataflow Op args past sigs'
  route : Route args (extend past sigs) (extend past sigs')
  shorter : sigs'.length + 1 = sigs.length

/-- Attempt one deletion, checking every operand in the surviving suffix.
Bindings before the candidate can only read their own earlier scopes. -/
def erase? :
    {past sigs : List (List (Ty Data))} → {flow : Dataflow Op args past sigs} → {out : ValueSort Data} →
      Producer flow out → Option (Erasure Op args past sigs)
  | _, _, _, out, .here (rest := rest) =>
    (routeSuffix? rest (drop [(.value out : Ty Data)])).map fun (suffix, route) =>
      ⟨_, suffix, route, rfl⟩
  | _, _, _, _, .later (op := opcode) (inputs := operands) candidate =>
    (erase? candidate).map fun tail =>
      ⟨_, .cons opcode operands tail.flow, tail.route, congrArg Nat.succ tail.shorter⟩

variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}

structure DeletedLoop (Op : Signature.{u,v} Data)
    (inputs carried : List (ValueSort Data)) (entrySigs : List (List (Ty Data))) (out : ValueSort Data) where
  headerSigs : List (List (Ty Data))
  graph : Loop.Graph Op inputs carried entrySigs headerSigs out

variable {removed : ValueSort Data}

def rebuild (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (header : Erasure Op (Loop.headerPorts inputs carried) [] headerSigs)
    (predicate : Origin (Loop.headerPorts inputs carried) (extend [] header.sigs') (.value .predicate))
    (feedback : Wires (Loop.headerPorts inputs carried) (extend [] header.sigs') (dataPorts carried))
    (result : Origin (Loop.headerPorts inputs carried) (extend [] header.sigs') (.value out)) :
    DeletedLoop Op inputs carried entrySigs out :=
  ⟨header.sigs', {
    preheader := loop.preheader
    header := header.flow
    phiInputs
      | .entry => loop.phiInputs .entry
      | .backedge => feedback
    predicate := predicate
    result := result }⟩

/-- Delete a producer only when the surviving operands and every header
observation can be routed through its removal. -/
def delete? (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (candidate : Producer loop.header removed) : Option (DeletedLoop Op inputs carried entrySigs out) :=
  (erase? candidate).bind fun header =>
    (header.route loop.predicate).bind fun predicate =>
      (Route.wires? header.route (loop.phiInputs .backedge)).bind fun feedback =>
        (header.route loop.result).map fun result => rebuild loop header predicate feedback result

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion
