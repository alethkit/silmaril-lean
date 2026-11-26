module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Defs

/-! # Finite tables with closed constructor assignments -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables.Multiple

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open UnitSumSquare (Shape)
open UnitSumSquare.Cycles.Mixed (cutTags)
open ForwardingTables (obj inj table)

variable {κ X : Type*}

/-- The last assignment wins. Absence of an assignment forwards the input. -/
def thenReset (before after : Option κ) : Option κ :=
  match after with
  | none => before
  | some x => some x

structure Code (κ X : Type*) where
  tag : X
  reset : Option κ

abbrev StateCode (κ : Type*) (A : Shape) := Code κ A.Row
abbrev OutputCode (κ : Type*) (B A : Shape) := Code κ (Sum B.Row A.Row)

/-- Supply the assignment performed before this row or run. -/
def Code.withInput (o : Code κ X) (before : Option κ) : Code κ X :=
  ⟨o.tag, thenReset before o.reset⟩

/-- Apply a state map to a recurrence. Outward exits bypass it. -/
def Code.mapState {B A D : Shape} (rows : A.Row → StateCode κ D) :
    OutputCode κ B A → OutputCode κ B D
  | ⟨.inl b, m⟩ => ⟨.inl b, m⟩
  | ⟨.inr i, m⟩ => ⟨.inr (rows i).tag, thenReset m (rows i).reset⟩

/-- Run at most the given number of rows. On exit the result carries the
last assignment on that path, or `none` if every row forwarded. -/
def run {B A : Shape} (p : A.Row → OutputCode κ B A) : Nat → A.Row → Option (StateCode κ B)
  | 0, _ => none
  | n + 1, i =>
    match (p i).tag with
    | .inl b => some ⟨b, (p i).reset⟩
    | .inr j => (run p n j).map (fun o => o.withInput (p i).reset)

def ReachesExit {B A : Shape} (p : A.Row → OutputCode κ B A) (i : A.Row) : Prop :=
  ∃ fuel o, run p fuel i = some o

/-- Mark cut edges on the tags while retaining their original assignments. -/
def cutRows {B A : Shape} (p : A.Row → OutputCode κ B A) (mark : A.Row → Bool) :
    A.Row → OutputCode κ (.sum B A) A :=
  fun i => ⟨cutTags (fun j => (p j).tag) mark i, (p i).reset⟩

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

abbrev ClosedValue (Φ : Type v) (P : τ) := {w : Tm Φ // Tm.BranchValue [] w P}

/-- Interpret a closed constructor assignment or a forwarding action. -/
noncomputable def action (P : τ) : Option (ClosedValue Φ P) → (ofType (Φ := Φ) P ⟶ ofType P)
  | none => 𝟙 _
  | some w => ResetTables.action w.property .literal

noncomputable def stateMap (P : τ) (A D : Shape) (rows : A.Row → StateCode (ClosedValue Φ P) D) :
    obj (Φ := Φ) P A ⟶ obj P D :=
  table P A fun i => action P (rows i).reset ≫ inj P D (rows i).tag

noncomputable def outputWith (P : τ) (A : Shape) {B : Shape}
    {Y : Paper.TypeCategory (τ := τ) Φ} (exit : B.Row → (ofType P ⟶ Y))
    (row : OutputCode (ClosedValue Φ P) B A) : ofType P ⟶ Y ⨿ obj P A :=
  action P row.reset ≫ ForwardingTables.outputWith P A exit row.tag

noncomputable def stepWith (P : τ) (A : Shape) {B : Shape}
    {Y : Paper.TypeCategory (τ := τ) Φ} (exit : B.Row → (ofType P ⟶ Y))
    (rows : A.Row → OutputCode (ClosedValue Φ P) B A) : obj P A ⟶ Y ⨿ obj P A :=
  table P A (outputWith P A exit ∘ rows)

noncomputable abbrev output (P : τ) (B A : Shape) :
    OutputCode (ClosedValue Φ P) B A → (ofType P ⟶ obj (Φ := Φ) P B ⨿ obj P A) :=
  outputWith P A (inj P B)

noncomputable abbrev step (P : τ) (B A : Shape) (rows : A.Row → OutputCode (ClosedValue Φ P) B A) :
    obj (Φ := Φ) P A ⟶ obj P B ⨿ obj P A :=
  stepWith P A (inj P B) rows

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables.Multiple
