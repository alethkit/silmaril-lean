module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Thms

/-! # Bounded unfolding of a coded feedback table -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Termination

/-- Precompose the payload choice of an exit with an earlier choice. -/
def withInput {B : Shape} (p : Payload) (o : StateCode B) : StateCode B :=
  ⟨o.tag, p.then o.payload⟩

/-- Execute at most the given number of table rows. A successful run records
the outward tag and how its payload depends on the initial input. -/
def run {B A : Shape} (rows : A.Row → OutputCode B A) : Nat → A.Row → Option (StateCode B)
  | 0, _ => none
  | n + 1, i =>
    match (rows i).tag with
    | .inl j => some ⟨j, (rows i).payload⟩
    | .inr j => (run rows n j).map (withInput (rows i).payload)

/-- Every source row admits a finite successful run. The bound may depend on the row. -/
def Terminates {B A : Shape} (rows : A.Row → OutputCode B A) : Prop :=
  ∀ i, ∃ n o, run rows n i = some o

/-- A state map on tags that retains the input payload on every branch. -/
def forwardingRows {A D : Shape} (k : A.Row → D.Row) (i : A.Row) : StateCode D :=
  ⟨k i, .forward⟩

namespace MergeFibers

abbrev result : Shape := .unit
abbrev target : Shape := .sum .unit .unit
abbrev source : Shape := .sum target target

/-- Each of the two source fibers maps to one target state. -/
def tags : source.Row → target.Row
  | .inl _ => .inl ()
  | .inr _ => .inr ()

/-- The two left states recur to different right states. Both right states exit. -/
def sourceRows : source.Row → OutputCode result source
  | .inl i => ⟨.inr (.inr i), .forward⟩
  | .inr _ => ⟨.inl (), .forward⟩

/-- The target recurs from left to right, then exits. -/
def targetRows : target.Row → OutputCode result target
  | .inl () => ⟨.inr (.inr ()), .forward⟩
  | .inr () => ⟨.inl (), .forward⟩

end MergeFibers

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Termination
