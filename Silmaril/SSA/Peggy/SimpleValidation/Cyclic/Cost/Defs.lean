module

public import Silmaril.SSA.Peggy.EPEG.Selection.Defs
public import Silmaril.SSA.Peggy.EPEG.Selection.Legality.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Defs
public import Init.Data.List.MinMaxOn

/-! # Cost selection over checked single-loop PEG candidates -/

@[expose] public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost

open PEG
open EPEG (Classes Selection)
open EPEG.Selection (FeedbackRank Row)
open PEG.Simple.Revert.While
open RVSDG (Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {source : Graph P params [result] n 1}

/-- Materialized graph with a typed representative assignment and common-row
evidence. Class membership, demands, cycles and scheduling are checked later. -/
structure Candidate (source : Graph P params [result] n 1) where
  size : Nat
  graph : Graph P params [result] size 1
  selection : Selection source graph
  rows : ∀ i, Row selection i

/-- Copy the selected labels and supply their new ordered wiring. The caller
chooses every representative and root. This construction does not check classes. -/
def Candidate.wire (source : Graph P params [result] n 1) {size : Nat}
    (rep : Fin size → Fin n)
    (args : ∀ i, Tuple (Ref (source.sort ∘ rep)) (source.node (rep i)).inputs)
    (roots : Tuple (Ref (source.sort ∘ rep)) [result]) : Candidate source :=
  let graph : Graph P params [result] size 1 :=
    ⟨source.forest, source.sort ∘ rep, fun i => Node.ofLabel (source.node (rep i)).label (args i), roots⟩
  let sel : Selection source graph :=
    ⟨fun i => Ref.ofId source.sort (rep i), Region.Automatic.inferDemandRank graph⟩
  ⟨size, graph, sel, fun i =>
    let row := source.node (rep i)
    ⟨row.inputs, row.label, row.args, args i, HEq.rfl, rfl⟩⟩

/-- Count primitive rows in the materialized table once per address. -/
def Candidate.primitiveRows (candidate : Candidate source) : Nat :=
  (List.finRange candidate.size).countP fun i =>
    match (candidate.graph.node i).label with
    | .op _ => true
    | _ => false

structure Legal (classes : Classes n) (candidate : Candidate source) where
  boundary : candidate.selection.check classes = true
  edges : Selection.checkRows candidate.rows classes = true
  feedback : FeedbackRank candidate.graph

def Candidate.checkLegal (classes : Classes n) (candidate : Candidate source) :
    Option (Legal classes candidate) := do
  let feedback ← FeedbackRank.infer candidate.graph
  if ok : candidate.selection.check classes = true ∧ Selection.checkRows candidate.rows classes = true then
    some ⟨ok.1, ok.2, feedback⟩
  else none

structure Accepted (source : Graph P params [result] n 1) (classes : Classes n) where
  candidate : Candidate source
  legal : Legal classes candidate
  reversion : Region.Certificate candidate.graph

def Accepted.output {classes : Classes n} (accepted : Accepted source classes) :
    PEG.Simple.Program P true params result :=
  accepted.reversion.revert

variable [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]

/-- Check the actual table, then obtain a checked primitive SIMPLE schedule
for one parentless loop and a single sampled return. -/
def Candidate.check (classes : Classes n) (candidate : Candidate source) :
    Option (Accepted source classes) :=
  match candidate.checkLegal classes with
  | none => none
  | some legal =>
    (Region.Automatic.extract candidate.graph).map fun reversion => ⟨candidate, legal, reversion⟩

/-- Keep the first accepted minimum in pool order. Empty or entirely
rejected pools have no result. -/
def select (classes : Classes n) (cost : Candidate source → Nat) (pool : List (Candidate source)) :
    Option (Accepted source classes) :=
  (pool.filterMap (Candidate.check classes)).minOn? (fun a => cost a.candidate)

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost
