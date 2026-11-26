module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.TwoExit.Defs

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit

open Morphism.CaseSSA (erase_hasType)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B : τ}

theorem toSSA_hasType_proof {n : Nat} {β : BoundCtx τ n} (c : TwoExit Φ A B β) :
    Region.HasType β.toList c.toSSA [A, B] := by
  induction c with
  | left a => exact .br rfl (erase_hasType a.2.toHasType)
  | right b => exact .br rfl (erase_hasType b.2.toHasType)
  | case e _ _ ihl ihr => exact .case (erase_hasType e.2.toHasType) ihl ihr
  | dispatch c =>
    apply (c.toSSA_hasType (L := [coprod A B]) (exit := 0) rfl).linkExits
    intro i X h
    cases i with
    | zero =>
      cases Option.some.inj h
      exact .case (.var rfl) (.br rfl (.var rfl)) (.br rfl (.var rfl))
    | succ i => simp [At] at h

end Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit
