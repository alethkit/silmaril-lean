module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Defs

/-! Dependency-triggered scheduling of the three equations of the pure diamond. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist

open Semantics.Dataflow (Flat)
open RVSDG (Tuple extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Ty Data))} {out : ValueSort Data}
variable {value : Data → Type w}

inductive Task where
  | producers
  | branch
  | phi
  deriving DecidableEq, Repr

/-- Processing a task costs more than all of the tasks it can enqueue. -/
def Task.weight : Task → Nat
  | .producers => 4
  | .branch => 2
  | .phi => 1

def potential : List Task → Nat
  | [] => 0
  | task :: pending => task.weight + potential pending

/-- Append a task when a watched input changed and the task is absent. -/
def schedule (changed : Prop) [Decidable changed] (task : Task) (pending : List Task) : List Task :=
  if changed ∧ task ∉ pending then pending ++ [task] else pending

/-- The two facts read by Phi. A fact from an unmarked occurrence cannot
trigger a rerun when producers change. -/
def phiInputs (g : Graph Op inputs sigs out)
    (entry : Tuple (Fact value) (dataPorts inputs)) (edges : Executable)
    (facts : ProducerFacts value (extend [] sigs)) : Flat (sortValue value out) × Flat (sortValue value out) :=
  (gate edges .first (readFact entry facts (g.phi.operand .first)),
    gate edges .second (readFact entry facts (g.phi.operand .second)))

def predicateFact (g : Graph Op inputs sigs out) (entry : Tuple (Fact value) (dataPorts inputs))
    (facts : ProducerFacts value (extend [] sigs)) : Flat (ULift.{w} Bool) :=
  readFact entry facts g.predicate

variable (m : Model.{u, v, w} Op) [DecidableEq (sortValue m.value out)]
variable (g : Graph Op inputs sigs out) (entry : Tuple (Fact m.value) (dataPorts inputs))

/-- Execute just one equation. The producer block is entry-dependent and
runs once, in the existing dependency order. Branch can wake Phi by
changing the executable set. Phi has no consumers in this profile. -/
def step : Task → State m.value sigs out → List Task → State m.value sigs out × List Task
  | .producers, (edges, old, result), pending =>
    let locals := evalFacts m entry g.dataflow PUnit.unit
    let new := factsOfLocals locals
    let pending := schedule (predicateFact g entry new ≠ predicateFact g entry old) .branch pending
    let pending := schedule (phiInputs g entry edges new ≠ phiInputs g entry edges old) .phi pending
    ((edges, new, result), pending)
  | .branch, (old, facts, result), pending =>
    let edges := branchEdges g.phi.merge (predicateFact g entry facts)
    ((edges, facts, result), schedule (edges ≠ old) .phi pending)
  | .phi, (edges, facts, _), pending =>
    ((edges, facts, phiFact g.phi edges entry facts), pending)

structure Run (value : Data → Type w) (sigs : List (List (Ty Data))) (out : ValueSort Data) where
  state : State value sigs out
  pending : List Task
  visits : List Task

/-- Pop one item at a time. Expose pending work so the termination theorem
can verify that the certified budget was sufficient. -/
def runSteps : Nat → State m.value sigs out → List Task → Run m.value sigs out
  | _, state, [] => ⟨state, [], []⟩
  | 0, state, task :: pending => ⟨state, task :: pending, []⟩
  | fuel + 1, state, task :: pending =>
    let next := step m g entry task state pending
    let run := runSteps fuel next.1 next.2
    {run with visits := task :: run.visits}

/-- Initially branch may read an argument. Phi already agrees with the
empty executable set and becomes pending only on a dependency change. -/
def initial : List Task := [.branch, .producers]

def run : Run m.value sigs out :=
  runSteps m g entry (potential initial) ⊥ initial

/-- The final fact assignment from the dependency-triggered run. -/
def solve : State m.value sigs out := (run m g entry).state

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Worklist
