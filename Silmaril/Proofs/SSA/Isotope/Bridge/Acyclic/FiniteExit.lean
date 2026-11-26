module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Defs

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Acyclic

open Morphism.CaseSSA (erase_hasType)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem Code.toSSA_renameLabels_proof {n : Nat} {β : BoundCtx τ n} {A : τ}
    (c : Code Φ β A) (ρ : Nat → Nat) (i : Nat) :
    (c.toSSA i).renameLabels ρ = c.toSSA (ρ i) := by
  induction c generalizing ρ i <;> simp_all [Code.toSSA, Region.renameLabels, DeBruijn.liftN, DeBruijn.lift]

theorem FiniteExit.toSSA_hasType_proof {L : LCtx τ} {n : Nat} {β : BoundCtx τ n}
    (c : FiniteExit Φ L β) : Region.HasType β.toList c.toSSA L := by
  induction c with
  | br h a => exact .br h (erase_hasType a.2.toHasType)
  | case e _ _ hl hr => exact .case (erase_hasType e.2.toHasType) hl hr
  | @join n β A a b hb =>
    apply (a.toSSA_hasType (L := [A]) (exit := 0) rfl).linkExits
    intro i X h
    cases i with
    | zero => cases Option.some.inj h; exact hb
    | succ i => simp [At] at h

theorem FiniteExit.exits_ne_nil_proof {L : LCtx τ} {n : Nat} {β : BoundCtx τ n}
    (c : FiniteExit Φ L β) : L ≠ [] := by
  induction c with
  | br h _ => intro e; simp [e, At] at h
  | case _ _ _ left _ => exact left
  | join _ _ body => exact body

theorem TwoExit.toSSA_toFinite_proof {A B : τ} {n : Nat} {β : BoundCtx τ n}
    (c : TwoExit Φ A B β) : c.toFinite.toSSA = c.toSSA := by
  induction c with
  | case a l r hl hr => simp only [TwoExit.toFinite, TwoExit.toSSA, FiniteExit.toSSA, hl, hr]
  | left | right | dispatch => rfl

end Silmaril.Isotope.LambdaSSA.Acyclic
