module

public import Silmaril.SSA.PEG.Semantics.Defs

/-! # Stream equality, merge certificates and selection for guarded PEGs -/

@[expose] public section

namespace Silmaril.SSA.Peggy.EPEG

open RVSDG (Port Tuple)

universe u v x

variable {Data : Type u} {P : PEG.InstructionSet.{u,v} Data}
variable {params results : List (PEG.Ty Data)} {n n' l : Nat}
variable {g : PEG.Graph P params results n l} {m : PEG.Interpretation.{u,v,x} P}

/-- Two vertices agree when their declared sorts agree and they have the
same partial value at every iteration vector. -/
def StreamEq (values : g.Valuation m) (a b : Fin n) : Prop :=
  g.sort a = g.sort b ∧ ∀ i, HEq (values (a, i)) (values (b, i))

/-- Class labels are finite vertex numbers. They need only identify a partition. -/
abbrev Classes (n : Nat) := Fin n → Fin n

namespace Classes

def discrete : Classes n := id

/-- Only pairs in the same class need to agree. Distinct classes may already
denote equal streams. -/
def Valid (classes : Classes n) (values : g.Valuation m) : Prop :=
  ∀ a b, classes a = classes b → StreamEq values a b

/-- Replace the whole class of `b` with the label of `a`. -/
def merge (classes : Classes n) (a b : Fin n) : Classes n :=
  fun v => classes (if classes v = classes b then a else v)

end Classes

structure Equation (g : PEG.Graph P params results n l) where
  lhs : Fin n
  rhs : Fin n
  sorted : g.sort lhs = g.sort rhs

def Equation.Holds (e : Equation g) (values : g.Valuation m) : Prop :=
  StreamEq values e.lhs e.rhs

/-- A ground rule on the concrete graph. Its guards and conclusion are
equalities of entire streams. -/
structure GuardedEquation (g : PEG.Graph P params results n l) where
  guards : List (Equation g)
  conclusion : Equation g

def GuardedEquation.Holds (rule : GuardedEquation g) (values : g.Valuation m) : Prop :=
  (∀ guard ∈ rule.guards, guard.Holds values) → rule.conclusion.Holds values

/-- The finite guard check reads established class equalities. The soundness
of the rule itself is supplied separately as `Holds`. -/
def GuardedEquation.check (rule : GuardedEquation g) (classes : Classes n) : Bool :=
  rule.guards.all fun guard => classes guard.lhs == classes guard.rhs

/-- A common label fixes the result, the ordered operand profile and every
loop identity. Each node retains its own typed references. -/
structure MatchingNodes (g : PEG.Graph P params results n l) (a b : Fin n) where
  inputs : List (PEG.Ty Data)
  out : PEG.Ty Data
  label : PEG.Label P params (Fin l) inputs out
  lhsArgs : Tuple (PEG.Ref g.sort) inputs
  rhsArgs : Tuple (PEG.Ref g.sort) inputs
  lhsSort : g.sort a = out
  rhsSort : g.sort b = out
  lhsNode : HEq (g.node a) (PEG.Node.ofLabel label lhsArgs)
  rhsNode : HEq (g.node b) (PEG.Node.ofLabel label rhsArgs)

def MatchingNodes.checkOperands {a b : Fin n} (pair : MatchingNodes g a b)
    (classes : Classes n) : Bool :=
  (List.finRange pair.inputs.length).all fun k =>
    classes (pair.lhsArgs.get (PEG.portAt pair.inputs k)).id ==
      classes (pair.rhsArgs.get (PEG.portAt pair.inputs k)).id

/-- A candidate table with the same ordered boundary and loop frame. Each
of its vertices names a typed source representative. -/
structure Selection (source : PEG.Graph P params results n l)
    (target : PEG.Graph P params results n' l) where
  representative : (v : Fin n') → PEG.Ref source.sort (target.sort v)
  rank : PEG.DemandRank n' l

namespace Selection

variable {target : PEG.Graph P params results n' l}

def sourceRef (candidate : Selection g target) {t : PEG.Ty Data}
    (ref : PEG.Ref target.sort t) : PEG.Ref g.sort t :=
  let rep := candidate.representative ref.id
  ⟨rep.id, rep.typed.trans ref.typed⟩

/-- Admission checks the actual candidate's demands and pairs all roots
with their selected source classes, in result order. -/
def check (candidate : Selection g target) (classes : Classes n) : Bool :=
  candidate.rank.check target &&
    (List.finRange results.length).all fun i =>
      let p := PEG.portAt results i
      classes (g.roots.get p).id == classes (candidate.sourceRef (target.roots.get p)).id

/-- Pull back source streams along the representative assignment. A semantic
certificate must prove that this valuation solves the candidate's equations. -/
def inherit (candidate : Selection g target) (values : g.Valuation m) : target.Valuation m :=
  fun q =>
    let ref := candidate.representative q.1
    ref.read m.carrier (values (ref.id, q.2))

end Selection
end Silmaril.SSA.Peggy.EPEG
