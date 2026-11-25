module

public import Silmaril.Logic.Operational.SOS.Marked.Defs

@[expose] public section

namespace Silmaril.Logic.Operational.SOS.Marked.Proofs

open CategoryTheory
open Silmaril.Semantics.Operational (Outcome)

universe u

theorem judgment_id (A : Carriers.{u}) (j : Judgment A) :
    Carriers.Hom.judgment (𝟙 A) j = j := by
  cases j with
  | step _ => rfl
  | entry _ _ => rfl
  | endpoint _ o => cases o <;> rfl

theorem judgment_comp {A B C : Carriers.{u}} (f : A ⟶ B) (g : B ⟶ C) (j : Judgment A) :
    Carriers.Hom.judgment (f ≫ g) j = g.judgment (f.judgment j) := by
  cases j with
  | step _ => rfl
  | entry _ _ => rfl
  | endpoint _ o => cases o <;> rfl

end Silmaril.Logic.Operational.SOS.Marked.Proofs
