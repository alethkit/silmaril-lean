module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Defs

/-! # Finite constructor tables for a changing-state feedback square -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.FiniteSquare

open Silmaril CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open scoped Paper.BoundSimulation.Obstruction

local notation "obj" => ofType (Φ := Empty)

abbrev U : Ty Empty := .unit
abbrev S : Ty Empty := .coprod U U
abbrev D : Ty Empty := .coprod S U

/-- The source state embeds in the left arm of the target state. -/
noncomputable def embedding : obj S ⟶ obj D :=
  ofRegion (r := .br 0 (.inl (.var 0))) (.br rfl (.inl (.var rfl)))

/-- An instruction-free update requiring sequencing under an injection. -/
def update : Tm Empty := .inl (.let₁ (.var 0) (.var 0))

theorem update_normalizes :
    UnaryReturn.Beta.Constructors.Normalizes [S] update (.inl (.var 0)) D :=
  .inl (.ofBeta (.let₁ (.value (.var (i := 0) rfl)) (.value (.var (i := 0) rfl))))

/-- Turn two singleton arrows into a case table on the exact sum type. -/
noncomputable def table {A B : Ty Empty} {X : Paper.TypeCategory Empty}
    (l : obj A ⟶ X) (r : obj B ⟶ X) :
    obj (Silmaril.coprod A B) ⟶ X :=
  (sumIso A B).hom ≫ coprod.desc l r

/-- Return literal unit, independently of the input. -/
noncomputable def unitOutput : obj U ⟶ obj U :=
  ofRegion (r := .br 0 .unit) (.br rfl .unit)

/-- Two source states with literal unit payloads. -/
noncomputable def sourceState (b : Bool) : obj U ⟶ obj S :=
  match b with
  | false => ofRegion (r := .br 0 (.inl .unit)) (.br rfl (.inl .unit))
  | true => ofRegion (r := .br 0 (.inr .unit)) (.br rfl (.inr .unit))

/-- None exits; some recurs at the indicated source state. -/
noncomputable def sourceOutput (o : Option Bool) :
    obj U ⟶ obj U ⨿ obj S :=
  match o with
  | none => unitOutput ≫ coprod.inl
  | some b => sourceState b ≫ coprod.inr

/-- The target may exit, recur in the additional state, or recur in either embedded state. -/
noncomputable def targetOutput (o : Option (Option Bool)) :
    obj U ⟶ obj U ⨿ obj D :=
  match o with
  | none => unitOutput ≫ coprod.inl
  | some none => ofRegion (r := .br 0 (.inr .unit)) (.br rfl (.inr .unit)) ≫ coprod.inr
  | some (some b) => sourceState b ≫ embedding ≫ coprod.inr

/-- Two source rows, indexed by the source sum tag (false is left). -/
noncomputable def sourceStep (p : Bool → Option Bool) :
    obj S ⟶ obj U ⨿ obj S :=
  table (sourceOutput (p false)) (sourceOutput (p true))

/-- Two target rows on the embedded states; the extra state may have any guarded body. -/
noncomputable def targetStep (q : Bool → Option (Option Bool))
    (extra : obj U ⟶ obj U ⨿ obj D) :
    obj D ⟶ obj U ⨿ obj D :=
  table (table (targetOutput (q false)) (targetOutput (q true))) extra

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.FiniteSquare
