module

public import Silmaril.SSA.RVSDG.Theta.Defs
public import Silmaril.SSA.RVSDG.Categorical.Defs
public import Silmaril.Semantics.Categories.Thms
public import Silmaril.Semantics.Elgot.Thms

/-! # Categorical denotation of whole-region θ

The body computes the next tuple and a continuation tag. The stop tag routes
the tuple to the left coproduct summand. The continue tag routes it to the
right summand. Elgot iteration of this step denotes the loop.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Theta

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory

universe u v d h c k
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {D : Type d} {C : Type c} [Category.{h} D] [CartesianMonoidalCategory D]
  [Category.{k} C] [HasBinaryCoproducts C]
variable (J : D ⥤ C) [PreservesFiniteCoproducts J]
variable (m : Categorical.Model Op D)
variable {carried : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

/-- The stop tag selects external return, and the continue tag selects feedback. -/
noncomputable def routingCocone (X : D) :
    Cocone ((Discrete.functor (fun _ : Fin 2 => X)) ⋙ J) where
  pt := J.obj X ⨿ J.obj X
  ι :=
    { app := fun i => Fin.cases coprod.inl (fun _ => coprod.inr) i.as
      naturality := by
        rintro ⟨i⟩ ⟨j⟩ f
        obtain rfl : i = j := Discrete.eq_of_hom f
        have hf : f = 𝟙 _ := Subsingleton.elim _ _
        rw [hf]
        simp }

noncomputable def route (sel : Categorical.Selectors D) (X : D) :
    J.obj (sel.obj 2 ⊗ X) ⟶ J.obj X ⨿ J.obj X :=
  (isColimitOfPreserves J (sel.colimit 2 X)).desc (routingCocone J X)

/-- Route the result of one body execution to return or feedback. -/
noncomputable def step
    (body : J.obj (m.ports carried) ⟶ J.obj (m.ports (BodyResults carried))) :
    J.obj (m.ports carried) ⟶ J.obj (m.ports carried) ⨿ J.obj (m.ports carried) :=
  body ≫ route J m.selectors (m.ports carried)

/-- Interpret the inductive body and close its feedback with Elgot iteration. -/
noncomputable def Term.denote [Iteration C] (t : Term Op carried sigs) :
    J.obj (m.ports carried) ⟶ J.obj (m.ports carried) :=
  iterate (step J m (J.map (t.body.denote m)))

/-- Interpret the numbered body table directly and close its feedback. -/
noncomputable def Graph.denote [Iteration C] (g : Graph Op carried sigs) :
    J.obj (m.ports carried) ⟶ J.obj (m.ports carried) :=
  iterate (step J m (J.map (g.body.denote m)))

universe w

/-- The pure embedding into the repository's Kleisli category of partial values. -/
abbrev partJ := Kleisli.Adjunction.toKleisli (ofTypeMonad (_root_.Part : Type w → Type w))

/-- Observe the partial value of a categorical loop on an encoded runtime tuple. -/
noncomputable def Graph.denotePart (g : Graph Op carried sigs) (runtime : Model.{u, v, w} Op)
    (input : Tuple runtime.Val carried) : _root_.Part (Categorical.portsObj runtime.Val carried) :=
  (g.denote partJ (Categorical.Model.ofRuntime runtime)).of (Categorical.pack input)

end Silmaril.SSA.RVSDG.Theta
