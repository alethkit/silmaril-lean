module

public import Silmaril.SSA.PEG.Simple.Revert.Defs
public import Init.Data.List.Sort
public import Init.Data.Vector.Basic

/-! # Automatic scheduling for ranked, loop-free PEGs

Within each scope, visit demanded vertices in descending rank to expose
strict dependencies, then emit the selected bindings in reverse order.
A φ starts two new scopes from its selected operand and the bindings
already in scope at the branch. The existing checker validates the plan.
-/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.Automatic

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {result : Ty Data} {n : Nat}

def order (rank : Fin n → Nat) : List (Fin n) :=
  (List.finRange n).mergeSort (fun a b => rank b ≤ rank a)

def operands (g : Graph P params [result] n 0) (i : Fin n) : List (Fin n) :=
  (List.finRange (g.node i).inputs.length).map fun s => ((g.node i).arg s).id

def heightStep (g : Graph P params [result] n 0) (rank : Vector Nat n) : Vector Nat n :=
  Vector.ofFn fun i => (operands g i).foldl (fun h j => max h (rank[j.val] + 1)) 0

def heights (g : Graph P params [result] n 0) (rounds : Nat) : Vector Nat n :=
  Nat.repeat (heightStep g) rounds (Vector.replicate n 0)

/-- Infer a candidate rank by taking the maximum dependency height for
`n` rounds. The final checker independently validates the rank. -/
def inferRank (g : Graph P params [result] n 0) : Fin n → Nat := fun i => (heights g n)[i.val]

/-- Filter a descending list, adding the strict dependencies when their
consumer is selected. Already available bindings need no new demand hint. -/
def demandedRows (g : Graph P params [result] n 0) :
    List (Fin n) → List (Fin n) → List (Fin n)
  | [], _ => []
  | i :: rows, needed =>
    if i ∈ needed then i :: demandedRows g rows (strictInputs g i ++ needed)
    else demandedRows g rows needed

def emitReveals : List (Fin n) → Plan n → Plan n
  | [], next => next
  | i :: rows, next => .reveal i (emitReveals rows next)

/-- Nonempty only on φ. The checked label fixes the positions of its arms. -/
def arms (g : Graph P params [result] n 0) (i : Fin n) : Option (Fin n × Fin n) :=
  match g.node i with
  | ⟨_, .phi, args⟩ => some ((args.get (.tail .head)).id, (args.get (.tail (.tail .head))).id)
  | _ => none

/-- Thread a global writer budget through both arms and the continuation.
Every admitted schedule has at most one writer per graph vertex. -/
def emitBindings (g : Graph P params [result] n 0)
    (armPlan : List (Fin n) → Fin n → Nat → Option (Plan n × Nat)) :
    List (Fin n) → List (Fin n) → Nat → Option (Plan n × Nat)
  | [], _, budget => some (.done, budget)
  | _ :: _, _, 0 => none
  | i :: rows, live, budget + 1 => do
    match arms g i with
    | none =>
      let (next, left) ← emitBindings g armPlan rows (i :: live) budget
      return (.bind i next, left)
    | some (yes, no) =>
      let (yesCode, left) ← armPlan live yes budget
      let (noCode, left) ← armPlan live no left
      let (next, left) ← emitBindings g armPlan rows (i :: live) left
      return (.branch i yesCode noCode next, left)

def planScope (g : Graph P params [result] n 0) (rows : List (Fin n)) :
    Nat → List (Fin n) → Fin n → Nat → Option (Plan n × Nat)
  | 0, _, _, _ => none
  | fuel + 1, live, target, budget => do
    let demanded := demandedRows g (rows.filter fun i => i ∉ live) [target]
    let (body, left) ← emitBindings g (planScope g rows fuel) demanded.reverse live budget
    return (emitReveals demanded body, left)

def plan (g : Graph P params [result] n 0) (rank : Fin n → Nat) : Option (Plan n) :=
  (planScope g (order rank) (n + 1) [] (returnRef g).id n).map Prod.fst

/-- Synthesize the plan, then apply the Fig. 19 rank, scope, demand and
sharing checks from the certificate interface. -/
def checkRanked (g : Graph P params [result] n 0) (rank : Fin n → Nat) :
    Option (Certificate g) :=
  if DemandRank.check [.phase rank] g then
    match plan g rank with
    | none => none
    | some code => Certificate.check g rank code
  else none

/-- Infer both the rank and the schedule from the typed graph. -/
def check (g : Graph P params [result] n 0) : Option (Certificate g) :=
  checkRanked g (inferRank g)

/-- The straight-line subfragment permits all parameter and primitive
profiles, arbitrary vertex numbering, dead rows and repeated wires. -/
def StraightLine (g : Graph P params [result] n 0) : Prop :=
  ∀ i, arms g i = none

end Silmaril.SSA.PEG.Simple.Revert.Automatic
