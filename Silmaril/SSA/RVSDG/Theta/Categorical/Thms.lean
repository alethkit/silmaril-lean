module

public import Silmaril.SSA.RVSDG.Theta.Categorical.Defs
public import Silmaril.SSA.RVSDG.Theta.Thms
import Silmaril.Proofs.SSA.RVSDG.Theta.Categorical.Adequacy

/-! # Categorical θ agreement and partial-value adequacy -/

public section

namespace Silmaril.SSA.RVSDG.Theta

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w d h c k
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {carried : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

section Category

variable {D : Type d} {C : Type c} [Category.{h} D] [CartesianMonoidalCategory D]
  [Category.{k} C] [HasBinaryCoproducts C]
variable (J : D ⥤ C) [PreservesFiniteCoproducts J]

/-- A mapped tag selects its prescribed summand and preserves the payload. -/
theorem route_leg (sel : Categorical.Selectors D) (X : D) (i : Fin 2) :
    J.map (Categorical.selectorLeg (sel.tag i) : X ⟶ sel.obj 2 ⊗ X) ≫ route J sel X =
      Fin.cases coprod.inl (fun _ => coprod.inr) i :=
  Proofs.route_leg J sel X i

/-- The two categorical loop representations agree at their fixed numbering. -/
theorem Graph.denote_toTerm [Iteration C] (m : Categorical.Model Op D) (g : Graph Op carried sigs) :
    g.toTerm.denote J m = g.denote J m :=
  Proofs.denote_toTerm J m g

/-- Unfolding the loop starts by evaluating its body once. -/
theorem Graph.denote_unfold [HasFiniteCoproducts C] [Iteration C] [ElgotCategory C]
    (m : Categorical.Model Op D) (g : Graph Op carried sigs) :
    g.denote J m = step J m (J.map (g.body.denote m)) ≫ coprod.desc (𝟙 _) (g.denote J m) :=
  ElgotCategory.fixpoint _

end Category

/-- In the partial-value model, denotation returns exactly the operational
finite results of the θ graph. -/
theorem Graph.mem_denotePart (g : Graph Op carried sigs) (m : Model.{u, v, w} Op)
    (input output : Tuple m.Val carried) :
    Categorical.pack output ∈ g.denotePart m input ↔ g.Returns m input output :=
  Proofs.mem_denote m g input output

/-- A finite result determines the entire partial value. -/
theorem Graph.denotePart_eq_some (g : Graph Op carried sigs) (m : Model.{u, v, w} Op)
    (input output : Tuple m.Val carried) :
    g.denotePart m input = _root_.Part.some (Categorical.pack output) ↔ g.Returns m input output :=
  _root_.Part.eq_some_iff.trans (g.mem_denotePart m input output)

/-- For total deterministic primitives, the partial value is undefined
exactly for an infinite sequence of continuing body completions. -/
theorem Graph.denotePart_eq_none (g : Graph Op carried sigs) (m : Model.{u, v, w} Op)
    (input : Tuple m.Val carried) :
    g.denotePart m input = _root_.Part.none ↔ g.Diverges m input :=
  Proofs.denote_none_iff m g input

end Silmaril.SSA.RVSDG.Theta
