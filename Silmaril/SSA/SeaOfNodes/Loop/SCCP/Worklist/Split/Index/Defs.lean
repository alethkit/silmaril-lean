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

variable {g : Graph Op inputs carried entrySigs headerSigs out}

/-- Entry and feedback mark changes reach every Φ because each watches both
marks. Carried changes reach only indexed destinations and only with feedback enabled. -/
def destinations [eqBank : BankDecidableEq value (dataPorts carried)] (index : Index g)
    (old new : State value carried out) : Finset (Phi.Job carried) :=
  if (incomingIndex .entry ∈ old.1 ↔ incomingIndex .entry ∈ new.1) ∧
      (incomingIndex .backedge ∈ old.1 ↔ incomingIndex .backedge ∈ new.1) then
    if incomingIndex .backedge ∈ new.1 then
      letI (field : Phi.Job carried) : DecidableEq (Fact value (dataPorts carried)[field]) :=
        @Semantics.Dataflow.instDecidableEqFlat _ (eqBank.atPort field)
      (Finset.univ.filter fun field => new.2.1 field ≠ old.2.1 field).biUnion
        fun field => index.readers[field.val]
    else ∅
  else Finset.univ

variable (m : Model.{u, v, w} Op) [BankDecidableEq m.value (dataPorts carried)]
variable (input : Tuple (Fact m.value) (dataPorts inputs))

/-- Keep the pending prefix and append control, sorted Φ destinations and result.
The control and result watches remain the original gated whole-bank watches. -/
def wake (index : Index g) (old new : State m.value carried out) (pending : List (Task carried)) :
    List (Task carried) :=
  let notified := (index.destinations old new).sort.map Job.phi
  FIFO.wake (.control :: notified ++ [.result]) (fun
    | .control => decide (Worklist.dependencies new .control ≠ Worklist.dependencies old .control)
    | .phi _ => true
    | .result => decide (Worklist.dependencies new .result ≠ Worklist.dependencies old .result)) pending

def step (index : Index g) (job : Task carried) (state : State m.value carried out)
    (pending : List (Task carried)) : State m.value carried out × List (Task carried) :=
  let new := Split.update m g input job state
  (new, wake m index state new pending)

def runSteps (index : Index g) : Nat → State m.value carried out → List (Task carried) → Run m.value carried out :=
  FIFO.runSteps (step m input index)

def run (index : Index g) : Run m.value carried out :=
  runSteps m input index (potential (⊥ : State m.value carried out) initial) ⊥ initial

def solve (index : Index g) : State m.value carried out := (run m input index).state

end Index
end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split
