module

public import Silmaril.SSA.RVSDG.NestedTheta.Categorical.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Categorical.Adequacy

/-! # Categorical finite-return adequacy of nested γ and θ -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta

open CategoryTheory

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs carried : Ports (PortType V S)}
variable {past sigs : List (Ports (PortType V S))}
variable {M : Type (max u w) → Type (max u w)}

set_option backward.isDefEq.respectTransparency false in
/-- The step used in the fold closes by iteration of the chosen computation coproduct. -/
theorem iterate_stepArrow [_root_.Monad M] [LawfulMonad M] [Silmaril.Elgot.Iterate M]
    (m : Model.{u, v, w} Op) (body : Tuple m.Val carried → M (Tuple m.Val (Theta.BodyResults carried))) :
    ⇑(CategoryTheory.iterate (stepArrow m body)).of = Silmaril.Elgot.iter (step m body) := by
  rw [Kleisli.Type.iterate_of]
  simp only [stepArrow, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Encoding a term as a numbered graph preserves its Kleisli arrow. -/
theorem Term.denote_toGraph [_root_.Monad M] [LawfulMonad M] [Silmaril.Elgot.Iterate M]
    (m : Model.{u, v, w} Op) (t : Term Op args [] sigs outs) :
    t.toGraph.denote (M := M) m = t.denote (M := M) m := by
  rw [Graph.denote, Term.toTerm_toGraph]

/-- In the partial-value model a returned tuple is exactly an unbounded finite derivation,
also at an open region prefix. -/
theorem Term.mem_denoteOpen (m : Model.{u, v, w} Op) (t : Term Op args past sigs outs)
    (input : Tuple m.Val args) (locals : Locals m.Val past) (output : Tuple m.Val outs) :
    output ∈ t.denoteOpen (M := _root_.Part) m input locals ↔ t.Exec m input locals output :=
  Categorical.Proofs.mem_denoteOpen m t input locals output

theorem Term.mem_denote (m : Model.{u, v, w} Op) (t : Term Op args [] sigs outs)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    output ∈ t.denotePart m input ↔ t.Returns m input output :=
  t.mem_denoteOpen m input PUnit.unit output

/-- Graph denotation returns exactly the results of the decoded graph's unbounded term relation. -/
theorem Graph.mem_denote (m : Model.{u, v, w} Op) (g : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    output ∈ g.denotePart m input ↔ g.toTerm.Returns m input output :=
  g.toTerm.mem_denote m input output

/-- A finite result determines the entire partial value and agrees with the direct graph evaluator
at a sufficient bound. -/
theorem Graph.denotePart_eq_some (m : Model.{u, v, w} Op) (g : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    g.denotePart m input = _root_.Part.some output ↔ g.Returns m input output :=
  _root_.Part.eq_some_iff.trans ((g.mem_denote m input output).trans (g.returns_iff m input output).symm)

/-- Undefinedness means no finite return derivation for any output. -/
theorem Graph.denotePart_eq_none (m : Model.{u, v, w} Op) (g : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) :
    g.denotePart m input = _root_.Part.none ↔ ∀ output, ¬g.toTerm.Returns m input output := by
  rw [_root_.Part.eq_none_iff]
  exact forall_congr' fun output => not_congr (g.mem_denote m input output)

end Silmaril.SSA.RVSDG.NestedTheta
