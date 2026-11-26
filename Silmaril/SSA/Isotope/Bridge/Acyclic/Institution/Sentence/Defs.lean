module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Defs

/-! # Exact structured equation maps over the LetCase signature category -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory
open LambdaSSA.Acyclic (Code Operand)

variable {τ ε : Type} [TypeFormers τ] {P Q : InstrSig τ ε}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

/-- Use the existing LetCase institution's translation of an exact operand.
Both the term and the data-valued derivation come from its initial algebra fold. -/
def mapOperand (g : P ⟶ Q) {n : Nat} {β : BoundCtx τ n} {A : τ}
    (a : Operand P.Instr β A) : Operand Q.Instr β A :=
  (PresSig.translate ((LetCase.pres Γ₀).map g)).map (i := ⟨n, β, A⟩) a

/-- Relabel the operands of a structured SSA program, preserving the types
and placement of all its binders and joins. -/
def mapCode (g : P ⟶ Q) : {n : Nat} → {β : BoundCtx τ n} → {A : τ} →
    Code P.Instr β A → Code Q.Instr β A
  | _, _, _, .br a => .br (mapOperand g a)
  | _, _, _, .let₁ a b => .let₁ (mapOperand g a) (mapCode g b)
  | _, _, _, .let₂ a b => .let₂ (mapOperand g a) (mapCode g b)
  | _, _, _, .case e l r => .case (mapOperand g e) (mapCode g l) (mapCode g r)
  | _, _, _, .join a b => .join (mapCode g a) (mapCode g b)

/-- Translate both sides of an exact equation along a fixed-type primitive map. -/
def mapEquation (g : P ⟶ Q) (e : SSAEquation P) : SSAEquation Q :=
  ⟨e.1, mapCode g e.2.1, mapCode g e.2.2⟩

end Silmaril.Isotope.Institution.Acyclic
