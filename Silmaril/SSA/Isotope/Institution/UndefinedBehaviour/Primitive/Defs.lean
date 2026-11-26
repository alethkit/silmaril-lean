module

public import Silmaril.SSA.Isotope.Institution.Ordered.Thms

/-! # Adjoining a unit-taking operation per result type to primitive instruction signatures -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Refinement.UB

open CategoryTheory

universe u

variable {τ ε : Type u} [HasUnit τ]

/-- Typing of the extended alphabet is independent of the chosen effect. -/
@[instance_reducible] def dialectTyping (P : InstrSig τ ε) : HasTy (P.Instr ⊕ τ) τ :=
  ⟨Sum.elim instrSrc (fun _ => Silmaril.unit), Sum.elim instrTrg id⟩

/-- Extend the primitive instruction alphabet at a fixed effect. In a unary instruction
syntax the canonical spelling of UB supplies literal unit. -/
abbrev dialect (P : InstrSig τ ε) (e : ε) : InstrSig τ ε where
  Instr := P.Instr ⊕ τ
  hasTy := dialectTyping P
  hasEff := ⟨Sum.elim instrEff (fun _ => e)⟩

/-- The original primitives retain their sources, targets and effects. -/
def includeDialect (P : InstrSig τ ε) (e : ε) : P ⟶ dialect P e where
  instr := Sum.inl
  source _ := rfl
  target _ := rfl
  effect _ := rfl

/-- Images for the new symbols must have the indicated source, target and effect. -/
abbrev UBInstruction (Q : InstrSig τ ε) (e : ε) (A : τ) :=
  {o : Q.Instr // instrSrc o = (Silmaril.unit : τ) ∧ instrTrg o = A ∧ instrEff o = e}

/-- Extend a relabelling by a chosen family of appropriately profiled instructions. -/
def extendDialect {P Q : InstrSig τ ε} {e : ε} (f : P ⟶ Q)
    (c : (A : τ) → UBInstruction Q e A) : dialect P e ⟶ Q where
  instr := Sum.elim (InstrSig.Hom.instr f) (fun A => (c A).val)
  source := Sum.rec (InstrSig.Hom.source f) (fun A => (c A).property.1)
  target := Sum.rec (InstrSig.Hom.target f) (fun A => (c A).property.2.1)
  effect := Sum.rec (InstrSig.Hom.effect f) (fun A => (c A).property.2.2)

end Silmaril.Isotope.Institution.Refinement.UB
