module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Defs

/-! # Guarded tables on finite coproducts of unit -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare

open Silmaril CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open scoped Paper.BoundSimulation.Obstruction

/-- An exact finite coproduct type, including the empty coproduct and any bracketing. -/
inductive Shape where
  | empty
  | unit
  | sum (left right : Shape)

def Shape.ty : Shape → Ty Empty
  | .empty => .empty
  | .unit => .unit
  | .sum a b => .coprod a.ty b.ty

/-- Indices of the unit summands. -/
def Shape.Row : Shape → Type
  | .empty => Empty
  | .unit => Unit
  | .sum a b => Sum a.Row b.Row

abbrev obj (A : Ty Empty) := ofType (Φ := Empty) A

/-- The syntactic tag of a row, with an explicit choice of payload. -/
def Shape.tagTerm : (A : Shape) → A.Row → Tm Empty → Tm Empty
  | .empty, i, _ => i.elim
  | .unit, _, a => a
  | .sum A _, .inl i, a => .inl (A.tagTerm i a)
  | .sum _ B, .inr j, a => .inr (B.tagTerm j a)

theorem Shape.tagValue (A : Shape) (i : A.Row) {Γ : VCtx (Ty Empty)} {a : Tm Empty}
    (h : Tm.BranchValue Γ a .unit) : Tm.BranchValue Γ (A.tagTerm i a) A.ty :=
  match A, i with
  | .empty, i => i.elim
  | .unit, _ => h
  | .sum A _, .inl i => .inl (A.tagValue i h)
  | .sum _ B, .inr j => .inr (B.tagValue j h)

noncomputable def branch {A B : Ty Empty} {a : Tm Empty} (ha : Tm.BranchValue [A] a B) :
    obj A ⟶ obj B :=
  ofRegion (.br (ℓ := 0) rfl ha)

/-- A summand injection forwards the input unit value. -/
noncomputable def Shape.inj (A : Shape) (i : A.Row) : obj .unit ⟶ obj A.ty :=
  branch (A.tagValue i (.var (i := 0) rfl))

/-- A constant row output uses literal unit as the payload. -/
noncomputable def Shape.literal (A : Shape) (i : A.Row) : obj .unit ⟶ obj A.ty :=
  branch (A.tagValue i .unit)

/-- Form a case table by successive singleton sum coproducts. -/
noncomputable def Shape.table {X : Paper.TypeCategory Empty} :
    (A : Shape) → (A.Row → (obj .unit ⟶ X)) → (obj A.ty ⟶ X)
  | .empty, _ =>
    ofRegion (r := .let₁ (.abort (.var 0)) (.br 0 (.var 0)))
      (.let₁ (.abort (.var (i := 0) rfl)) (.br rfl (.var (i := 0) rfl)))
  | .unit, rows => rows ()
  | .sum A B, rows =>
    (sumIso A.ty B.ty).hom ≫ coprod.desc (A.table (rows ∘ Sum.inl)) (B.table (rows ∘ Sum.inr))

/-- The left code exits and the right code recurs. Both use literal unit payloads. -/
noncomputable def output (B A : Shape) (o : Sum B.Row A.Row) :
    obj .unit ⟶ obj B.ty ⨿ obj A.ty :=
  (Shape.sum B A).literal o ≫ (sumIso B.ty A.ty).hom

/-- A guarded table with literal output in each row. -/
noncomputable def step (B A : Shape) (rows : A.Row → Sum B.Row A.Row) :
    obj A.ty ⟶ obj B.ty ⨿ obj A.ty :=
  A.table (output B A ∘ rows)

/-- A target table returns a literal on every row hit by the constructor map.
The remaining target rows can be arbitrary guarded arrows. -/
def HasLiteralTargets (B A D : Shape) {a : Tm Empty} (ha : Tm.BranchValue [A.ty] a D.ty)
    (rows : D.Row → (obj .unit ⟶ obj B.ty ⨿ obj D.ty)) : Prop :=
  ∀ (i : A.Row) (j : D.Row),
    (A.inj i ≫ branch ha = D.inj j ∨ A.inj i ≫ branch ha = D.literal j) →
    ∃ o : Sum B.Row D.Row, rows j = output B D o

/-- A row either forwards its input unit or emits literal unit. -/
inductive Payload where
  | forward
  | literal

def Payload.term : Payload → Tm Empty
  | .forward => .var 0
  | .literal => .unit

theorem Payload.value (p : Payload) : Tm.BranchValue [(Ty.unit : Ty Empty)] p.term .unit :=
  match p with
  | .forward => .var (i := 0) rfl
  | .literal => .unit

/-- Apply the output payload choice after the input payload choice. -/
def Payload.then (input : Payload) : Payload → Payload
  | .forward => input
  | .literal => .literal

/-- A tagged row arrow with a choice of unit payload. -/
noncomputable def Shape.emit (A : Shape) (i : A.Row) (p : Payload) : obj .unit ⟶ obj A.ty :=
  branch (A.tagValue i p.value)

/-- A code specifies an exit or recurrence tag and its payload choice. -/
structure OutputCode (B A : Shape) where
  tag : Sum B.Row A.Row
  payload : Payload

noncomputable def outputWithPayload (B A : Shape) (o : OutputCode B A) :
    obj .unit ⟶ obj B.ty ⨿ obj A.ty :=
  (Shape.sum B A).emit o.tag o.payload ≫ (sumIso B.ty A.ty).hom

noncomputable def stepWithPayload (B A : Shape) (rows : A.Row → OutputCode B A) :
    obj A.ty ⟶ obj B.ty ⨿ obj A.ty :=
  A.table (outputWithPayload B A ∘ rows)

/-- The target table has a coded output on the image of the constructor state map. -/
def HasTargetOutputs (B A D : Shape) {a : Tm Empty} (ha : Tm.BranchValue [A.ty] a D.ty)
    (rows : D.Row → (obj .unit ⟶ obj B.ty ⨿ obj D.ty)) : Prop :=
  ∀ (i : A.Row) (j : D.Row) (p : Payload),
    A.inj i ≫ branch ha = D.emit j p →
    ∃ o : OutputCode B D, rows j = outputWithPayload B D o

namespace Forwarding

abbrev source : Shape := .sum .unit .unit
abbrev target : Shape := .sum source .unit
abbrev result : Shape := .unit

/-- Embed the source state while retaining its unit payload. -/
def update : Tm Empty := .inl (.let₁ (.var 0) (.var 0))

theorem normalizes : UnaryReturn.Beta.Constructors.Normalizes [source.ty] update (.inl (.var 0))
    target.ty :=
  .inl (.ofBeta (.let₁ (.value (.var (i := 0) rfl)) (.value (.var (i := 0) rfl))))

/-- The left state recurs to the right state, which exits with its input payload. -/
def sourceRows : source.Row → OutputCode result source
  | .inl () => ⟨.inr (.inr ()), .forward⟩
  | .inr () => ⟨.inl (), .forward⟩

/-- The chosen payload applies to the exit from the embedded right state. -/
def targetRows (exitPayload : Payload) : target.Row → OutputCode result target
  | .inl (.inl ()) => ⟨.inr (.inl (.inr ())), .forward⟩
  | .inl (.inr ()) => ⟨.inl (), exitPayload⟩
  | .inr () => ⟨.inl (), .literal⟩

end Forwarding

namespace Collapse

abbrev source : Shape := .sum .unit .unit
abbrev target : Shape := .sum .unit .empty
abbrev result : Shape := .unit

/-- The two source tags both map to the unique target tag. -/
def update : Tm Empty := .inl (.let₁ (.var 0) .unit)

theorem normalizes : UnaryReturn.Beta.Constructors.Normalizes [source.ty] update (.inl .unit)
    target.ty :=
  .inl (.ofBeta (.let₁ (.value (.var (i := 0) rfl)) (.value .unit)))

/-- Each source state recurs on itself. -/
def sourceRows : source.Row → Sum result.Row source.Row := Sum.inr

/-- The unique target state also recurs on itself. -/
def targetRows : target.Row → Sum result.Row target.Row
  | .inl i => .inr (.inl i)
  | .inr i => i.elim

end Collapse

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare
