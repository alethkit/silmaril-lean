module

public import Silmaril.SSA.Peggy.Optimizer.Defs
public import Mathlib.Data.Finset.Card

/-! # Shared-row rewriting and ordered output validation -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Optimizer.Contextual

open Silmaril.Logic.Egg
open Bridge.Egg

variable {Data : Type} {P : PEG.InstructionSet.{0,0} Data}
variable {params results : List (PEG.Ty Data)} {out : PEG.Ty Data}
variable {rules : List (Core.Rule (signature P))}

/-- Collect the vertex identities in one rooted cone. Union counts even a
multiply referenced vertex just once. -/
def cone (p : RankedProgram P params results) (v : Fin p.size) : Finset (Fin p.size) :=
  insert v ((List.finRange (p.graph.node v).inputs.length).foldr
    (fun i seen => cone p ((p.graph.node v).arg i).id ∪ seen) ∅)
termination_by p.ranked.rank v
decreasing_by exact p.ranked.decreases v i

def reachable (p : RankedProgram P params results) : Finset (Fin p.size) :=
  (List.finRange results.length).foldr
    (fun slot seen => cone p (p.graph.roots.get (PEG.portAt results slot)).id ∪ seen) ∅

def isApplication {ts : List (PEG.Ty Data)} :
    PEG.Label P params (Fin 0) ts out → Bool
  | .param _ => false
  | .op _ | .phi => true
  | .theta l | .eval l | .pass l => l.elim0

/-- Count distinct reachable application vertices across the whole output
boundary. Undefined or unselected arms still contribute to this static cost. -/
def cost (p : RankedProgram P params results) : Nat :=
  ((reachable p).filter fun v => isApplication (p.graph.node v).label).card

def refTerm (p : RankedProgram P params results) (ref : PEG.Ref p.graph.sort out) :
    Term P params out := ref.typed ▸ encode p.ranked ref.id

/-- Replace one table row at the same address, so all incoming references
still share it. Recheck every dependency against the original rank. -/
def replace (p : RankedProgram P params results) (site : PEG.Ref p.graph.sort out)
    (row : PEG.Node P params (Fin 0) p.graph.sort out) : Option (RankedProgram P params results) :=
  let g : PEG.Graph P params results p.size 0 := { p.graph with
    node := fun v => if h : v = site.id then
      Eq.ndrec (motive := PEG.Node P params (Fin 0) p.graph.sort) row
        (site.typed.symm.trans (congrArg p.graph.sort h.symm))
      else p.graph.node v }
  (Acyclic.Ranked.check g p.ranked.rank).map fun ranked => ⟨p.size, g, ranked⟩

/-- An unchanged application lifts the child receipts using Egg congruence.
For φ, replay compares terms for the two arms. It performs no evaluation. -/
def liftReceipt {ins : List (PEG.Ty Data)} :
    (label : PEG.Label P params (Fin 0) ins out) →
      (∀ i : Fin ins.length, Core.Replay.Receipt rules (context params) ins[i]) →
      Core.Replay.Receipt rules (context params) out
  | .param slot, _ => .refl (encodeLabel (.param slot) (fun i => i.elim0))
  | .op op, children => .congr (.prim op) children
  | .phi, children => .congr (.phi _) children
  | .theta l, _ | .eval l, _ | .pass l, _ => l.elim0

/-- Rebuild the explanation from an old vertex, replacing every occurrence of
the selected address with the same rule receipt. -/
def receiptAt (p : RankedProgram P params results) (site : PEG.Ref p.graph.sort out)
    (rewrite : Core.Replay.Receipt rules (context params) out) (v : Fin p.size) :
    Core.Replay.Receipt rules (context params) (p.graph.sort v) :=
  if h : v = site.id then
    Eq.ndrec (motive := Core.Replay.Receipt rules (context params)) rewrite
      (site.typed.symm.trans (congrArg p.graph.sort h.symm))
  else
    liftReceipt (p.graph.node v).label fun i =>
      let arg := (p.graph.node v).arg i
      Eq.ndrec (motive := Core.Replay.Receipt rules (context params))
        (receiptAt p site rewrite arg.id) arg.typed
termination_by p.ranked.rank v
decreasing_by exact p.ranked.decreases v i

/-- Rule conclusions may have any sort, including one absent from the outputs. -/
abbrev Schema (P : PEG.InstructionSet.{0,0} Data) := Σ t : PEG.Ty Data, Rule P t

def core (entry : Schema P) : Core.Rule (signature P) := entry.2.core

abbrev Candidate (table : List (Schema P)) (p : RankedProgram P params results) :=
  CheckedProgram (table.map core) p

def propose [DecidableEq Data] (eqPrim : PrimitiveEq P) (table : List (Schema P))
    (p : RankedProgram P params results) (i : Fin table.length)
    (site : PEG.Ref p.graph.sort (table.get i).1)
    (found : TermMatch p (table.get i).2 (refTerm p site)) : Option (Candidate table p) := do
  let next ← replace p site (instantiateRow p (table.get i).2 found.binding)
  let step := mappedReceipt table core i (termSub found.binding)
  -- Bind every candidate root to the contextual receipt for its old root.
  CheckedProgram.verify eqPrim p next fun slot =>
    let root := p.graph.roots.get (PEG.portAt results slot)
    Eq.ndrec (motive := Core.Replay.Receipt (table.map core) (context params))
      (receiptAt p site step root.id) root.typed

def discover [DecidableEq Data] (eqPrim : PrimitiveEq P) (table : List (Schema P))
    (p : RankedProgram P params results) : List (Candidate table p) :=
  let live := reachable p
  (List.finRange table.length).flatMap fun i =>
    ((List.finRange p.size).filter fun v => v ∈ live).flatMap fun v =>
      match PEG.Ref.check p.graph.sort (table.get i).1 v.val with
      | none => []
      | some ref =>
        (matchTarget eqPrim p (table.get i).2 (refTerm p ref)).filterMap
          (propose eqPrim table p i ref)

def explore [DecidableEq Data] (eqPrim : PrimitiveEq P) (table : List (Schema P)) :
    Nat → (p : RankedProgram P params results) → List (Candidate table p) :=
  CheckedProgram.search (discover eqPrim table)

def optimize [DecidableEq Data] (eqPrim : PrimitiveEq P) (table : List (Schema P))
    (fuel : Nat) (p : RankedProgram P params results) : Candidate table p :=
  (explore eqPrim table fuel p).foldl (CheckedProgram.preferBy cost)
    (CheckedProgram.identity (table.map core) p)

/-- Independent validation for two admitted graphs whose corresponding
outputs unfold identically, including graphs with different sharing or numbering. -/
def compareOutputs [DecidableEq Data] (eqPrim : PrimitiveEq P)
    (source target : RankedProgram P params results) : Option (CheckedProgram [] source) :=
  CheckedProgram.verify eqPrim source target fun slot => .refl (encodeOutputs source.ranked slot)

end Silmaril.SSA.Peggy.Optimizer.Contextual
