module

public import Silmaril.SSA.Peggy.EPEG.Defs

/-! # Saturation over a finite table of merge obligations -/

@[expose] public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation

universe u v x

variable {Data : Type u} {P : PEG.InstructionSet.{u,v} Data}
variable {params results : List (PEG.Ty Data)} {n l : Nat}
variable {g : PEG.Graph P params results n l}

/-- Ground reasons over the fixed graph. Congruence binds both actual node
rows to a common label before the executable check compares their operands. -/
inductive Obligation (g : PEG.Graph P params results n l) where
  | guarded (rule : GuardedEquation g)
  | congruent {lhs rhs : Fin n} (pair : MatchingNodes g lhs rhs)

namespace Obligation

def endpoints : Obligation g → Fin n × Fin n
  | .guarded rule => (rule.conclusion.lhs, rule.conclusion.rhs)
  | .congruent (lhs := lhs) (rhs := rhs) _ => (lhs, rhs)

def check : Obligation g → Classes n → Bool
  | .guarded rule => rule.check
  | .congruent pair => pair.checkOperands

/-- The guard or operand check succeeds and this step joins two distinct classes. -/
def enabled (o : Obligation g) (c : Classes n) : Bool :=
  o.check c && (c o.endpoints.1 != c o.endpoints.2)

def merge (o : Obligation g) (c : Classes n) : Classes n :=
  c.merge o.endpoints.1 o.endpoints.2

/-- Guarded instances need laws over the supplied valuation. Congruence
uses the graph equations, which are a common premise of the soundness theorem. -/
def Holds {m : PEG.Interpretation.{u,v,x} P} (o : Obligation g) (values : g.Valuation m) : Prop :=
  match o with
  | .guarded rule => rule.Holds values
  | .congruent _ => True

end Obligation

/-- Partition inclusion. Labels can differ when both states identify the same pairs. -/
def Refines (c d : Classes n) : Prop :=
  ∀ a b, c a = c b → d a = d b

/-- Every obligation whose premises hold already has its conclusion in one class. -/
def Closed (os : List (Obligation g)) (c : Classes n) : Prop :=
  ∀ o ∈ os, o.check c = true → c o.endpoints.1 = c o.endpoints.2

def isClosed (os : List (Obligation g)) (c : Classes n) : Bool :=
  os.all fun o => !o.enabled c

/-- Select the first enabled obligation and remove just that occurrence.
Blocked items remain in the worklist for reconsideration after a merge. -/
def takeEnabled (c : Classes n) : List (Obligation g) → Option (Obligation g × List (Obligation g))
  | [] => none
  | o :: os =>
    if o.enabled c then some (o, os)
    else (takeEnabled c os).map fun (picked, rest) => (picked, o :: rest)

/-- Each unit of fuel pays for one merge. Termination with fuel zero still
returns a sound partition, and `isClosed` can distinguish a partial result. -/
def run : Nat → List (Obligation g) → Classes n → Classes n
  | 0, _, c => c
  | fuel + 1, os, c =>
    match takeEnabled c os with
    | none => c
    | some (picked, rest) => run fuel rest (picked.merge c)

/-- One unit per list occurrence suffices to reach closure. -/
def saturate (os : List (Obligation g)) (seed : Classes n) : Classes n :=
  run os.length os seed

end Silmaril.SSA.Peggy.EPEG.Saturation
