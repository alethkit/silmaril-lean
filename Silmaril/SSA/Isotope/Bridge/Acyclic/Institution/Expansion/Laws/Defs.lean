module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Defs

/-! # A necessary exact LetCase law for corridor expansion -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open Isotope.LetCase.LocallyNameless

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
  {n : Nat} {β : BoundCtx τ n} {A : τ} {t : Tm Empty P.Instr n}

/-- Let-η at the exact typing witness, binding and immediately returning the newest variable. -/
def letReturnEquation (d : Derivation P.Instr (Ctx.nil : Ctx Empty τ) β t A) : CaseEquation P :=
  ⟨⟨n, β, A⟩, ⟨.let₁ t (.bv 0), .let₁ d .bv⟩, ⟨t, d⟩⟩

/-- A raw operation algebra that distinguishes the let constructor from every
other constructor, regardless of the arguments. -/
def letReturnCountermodel (P : InstrSig τ ε) : CaseAlgebra P where
  Carrier _ := Bool
  op o _ := match o with
    | .let₁ _ _ => true
    | _ => false

/-- The closed unit instance of let-η. -/
def unitLetReturn (P : InstrSig τ ε) : CaseEquation P :=
  letReturnEquation (β := .nil) (.unit (Φ := P.Instr) (Γ := (Ctx.nil : Ctx Empty τ)))

end Silmaril.Isotope.Institution.Acyclic
