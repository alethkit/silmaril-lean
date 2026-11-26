module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Defs
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Union

/-! Reverse notifications for typed Φ jobs in the mixed single-loop FIFO. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {value : Data → Type w}

/-- An eager reverse table of typed Φ destinations for each carried operand. -/
structure Index (g : Graph Op inputs carried entrySigs headerSigs out) where
  readers : Vector (Finset (Phi.Job carried)) (dataPorts carried).length
  mem_readers : ∀ field dst, dst ∈ readers[field.val] ↔ field ∈ Phi.feedbackSupport g dst

namespace Index

/-- Build once per graph, sharing the ranked producer support table across destinations. -/
def build (g : Graph Op inputs carried entrySigs headerSigs out) : Index g :=
  let args := Phi.Support.headerPorts inputs carried
  let locals := Phi.Support.table args g.header PUnit.unit
  let supports := Vector.ofFn fun dst : Phi.Job carried =>
    Phi.Support.read args locals (Phi.wireAt (g.phiInputs .backedge) dst)
  { readers := Vector.ofFn fun field =>
      Finset.univ.filter fun dst => field ∈ supports[dst.val]
    mem_readers := by
      intro field dst
      simp [supports, args, locals, Phi.feedbackSupport, Phi.Support.wire] }

/-- Entry and feedback mark changes reach every Φ because each watches both
marks. Carried changes reach only indexed destinations and only with feedback enabled. -/
def gateDestinations {n : Nat} (old new : Executable)
    (readers : Unit → Finset (Fin n)) : Finset (Fin n) :=
  if (incomingIndex .entry ∈ old ↔ incomingIndex .entry ∈ new) ∧
      (incomingIndex .backedge ∈ old ↔ incomingIndex .backedge ∈ new) then
    if incomingIndex .backedge ∈ new then readers () else ∅
  else Finset.univ

variable {g : Graph Op inputs carried entrySigs headerSigs out}

/-- For an arbitrary pair of assignments, compare every carried coordinate
when feedback reads are enabled and the marks agree. -/
def destinations [eqBank : BankDecidableEq value (dataPorts carried)] (index : Index g)
    (old new : State value carried out) : Finset (Phi.Job carried) :=
  gateDestinations old.1 new.1 fun _ =>
    letI (field : Phi.Job carried) : DecidableEq (Fact value (dataPorts carried)[field]) :=
      @Semantics.Dataflow.instDecidableEqFlat _ (eqBank.atPort field)
    (Finset.univ.filter fun field => new.2.1 field ≠ old.2.1 field).biUnion
      fun field => index.readers[field.val]

/-- For a state and its one-job update, a Φ job can change only its own field.
Control and result jobs leave the bank unchanged. -/
def destinationsAfter [eqBank : BankDecidableEq value (dataPorts carried)] (index : Index g)
    (job : Task carried) (old new : State value carried out) : Finset (Phi.Job carried) :=
  gateDestinations old.1 new.1 fun _ =>
    match job with
    | .phi dst =>
      letI := @Semantics.Dataflow.instDecidableEqFlat _ (eqBank.atPort dst)
      if new.2.1 dst = old.2.1 dst then ∅ else index.readers[dst.val]
    | .control | .result => ∅

variable (m : Model.{u, v, w} Op) [BankDecidableEq m.value (dataPorts carried)]
variable (input : Tuple (Fact m.value) (dataPorts inputs))

/-- Keep the pending prefix and append control, sorted Φ destinations and result.
The control and result watches remain the original gated whole-bank watches. -/
def wakeDestinations (destinations : Finset (Phi.Job carried)) (old new : State m.value carried out)
    (pending : List (Task carried)) : List (Task carried) :=
  let notified := destinations.sort.map Job.phi
  FIFO.wake (.control :: notified ++ [.result]) (fun
    | .control => decide (Worklist.dependencies new .control ≠ Worklist.dependencies old .control)
    | .phi _ => true
    | .result => decide (Worklist.dependencies new .result ≠ Worklist.dependencies old .result)) pending

/-- Compare arbitrary old and new assignments and append their wakeups. -/
def wake (index : Index g) (old new : State m.value carried out) (pending : List (Task carried)) :
    List (Task carried) :=
  wakeDestinations m (index.destinations old new) old new pending

/-- Reference indexed step using the general assignment comparison. -/
def step (index : Index g) (job : Task carried) (state : State m.value carried out)
    (pending : List (Task carried)) : State m.value carried out × List (Task carried) :=
  let new := Split.update m g input job state
  (new, wake m index state new pending)

/-- A FIFO pop uses the job's write to locate a changed carried coordinate. -/
def stepLocal (index : Index g) (job : Task carried) (state : State m.value carried out)
    (pending : List (Task carried)) : State m.value carried out × List (Task carried) :=
  let new := Split.update m g input job state
  (new, wakeDestinations m (index.destinationsAfter job state new) state new pending)

def runSteps (index : Index g) : Nat → State m.value carried out → List (Task carried) → Run m.value carried out :=
  FIFO.runSteps (stepLocal m input index)

def run (index : Index g) : Run m.value carried out :=
  runSteps m input index (potential (⊥ : State m.value carried out) initial) ⊥ initial

def solve (index : Index g) : State m.value carried out := (run m input index).state

end Index
end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split
