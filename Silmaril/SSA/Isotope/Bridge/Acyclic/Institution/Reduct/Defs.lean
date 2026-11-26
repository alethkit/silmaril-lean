module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Defs

/-! # Primitive restriction of categorical interpretations -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {τ ε : Type} [TypeFormers τ] {P Q : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V] {J : V ⥤ C}
  {M : TypeModel τ V}

/-- Change the domain and codomain of a computation along exact type equalities. -/
def transportArrow {A A' B B' : τ} (hs : A = A') (ht : B = B')
    (f : J.obj (M.obj A) ⟶ J.obj (M.obj B)) :
    J.obj (M.obj A') ⟶ J.obj (M.obj B') :=
  cast (congrArg₂ (fun X Y => J.obj (M.obj X) ⟶ J.obj (M.obj Y)) hs ht) f

/-- Restrict primitive interpretation along an instruction relabelling. The
value model is shared, and the instruction's source and target are transported. -/
@[instance_reducible]
def restrictInstructions (g : P ⟶ Q) (I : InstructionModel J M Q.Instr) :
    InstructionModel J M P.Instr where
  denote f := transportArrow (J := J) (M := M) (g.source f) (g.target f) (I.denote (g.instr f))

end Silmaril.Isotope.Institution.Acyclic
