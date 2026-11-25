module

public import Silmaril.SSA.RVSDG.NestedTheta.Defs
public import Silmaril.Semantics.Categories.Thms

/-! # Nested RVSDG in a Kleisli computation category -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta

open CategoryTheory CategoryTheory.Limits
open Silmaril.Elgot (Iterate iter)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args ins outs carried : Ports (PortType V S)}
variable {past sigs : List (Ports (PortType V S))}
variable {M : Type (max u w) → Type (max u w)} [_root_.Monad M]

/-- Tag zero returns the payload, while tag one feeds it back. -/
def route (m : Model.{u, v, w} Op) :
    Tuple m.Val (Theta.BodyResults carried) → Tuple m.Val carried ⊕ Tuple m.Val carried
  | .cons tag payload => Fin.cases (.inl payload) (fun _ => .inr payload) tag.down

/-- Route the result of a complete body computation. A partial body may itself contain loops. -/
def step (m : Model.{u, v, w} Op)
    (body : Tuple m.Val carried → M (Tuple m.Val (Theta.BodyResults carried))) :
    Tuple m.Val carried → M (Tuple m.Val carried ⊕ Tuple m.Val carried) :=
  body >=> fun result => pure (route m result)

/-- Present the routed step at the chosen Kleisli coproduct. -/
noncomputable def stepArrow [LawfulMonad M] (m : Model.{u, v, w} Op)
    (body : Tuple m.Val carried → M (Tuple m.Val (Theta.BodyResults carried))) :
    Kleisli.mk (ofTypeMonad M) (Tuple m.Val carried) ⟶
      Kleisli.mk (ofTypeMonad M) (Tuple m.Val carried) ⨿
      Kleisli.mk (ofTypeMonad M) (Tuple m.Val carried) :=
  Kleisli.Hom.mk (↾(step (M := M) m body)) ≫ (Kleisli.Type.coprodIsoSum M _ _).inv

variable [Iterate M]

/-- A primitive is a pure value arrow, γ copairs its arms and θ iterates
the computation of its sole child in the computation category. -/
def Kind.denote (m : Model.{u, v, w} Op) :
    {ins outs : Ports (PortType V S)} → (kind : Kind Op ins outs) →
    (Fin kind.arity → Tuple m.Val kind.entry → M (Tuple m.Val kind.exit)) →
    Tuple m.Val ins → M (Tuple m.Val outs)
  | _, _, .base (.simple opcode), _, input => pure (m.run opcode input)
  | _, _, .base (.gamma _), arms, .cons tag payload => arms tag.down payload
  | _, _, .theta _, children, input => iter (step m (children (0 : Fin 1))) input

/-- A let retains its pure scope, runs the node once, and appends its result.
Child calls receive only the node's declared entry tuple. -/
def Term.denoteOpen (m : Model.{u, v, w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Term Op args past sigs outs → Tuple m.Val args → Locals m.Val past → M (Tuple m.Val outs)
  | _, _, _, _, .ret results, entry, locals => pure (results.read entry locals)
  | _, _, _, _, .bind node children rest, entry, locals => do
    let result ← node.kind.denote m
      (fun i input => (children i).denoteOpen m input PUnit.unit) (node.inputs.read entry locals)
    rest.denoteOpen m entry (locals.snoc result)

/-- Closed entry and exit tuples determine the source and target Kleisli objects. -/
def Term.denote [LawfulMonad M] (m : Model.{u, v, w} Op) (t : Term Op args [] sigs outs) :
    Kleisli.mk (ofTypeMonad M) (Tuple m.Val args) ⟶
      Kleisli.mk (ofTypeMonad M) (Tuple m.Val outs) :=
  Kleisli.Hom.mk (↾fun input => t.denoteOpen (M := M) m input PUnit.unit)

/-- The numbered graph is interpreted by its typed table decoder. -/
def Graph.denote [LawfulMonad M] (m : Model.{u, v, w} Op) (g : Graph Op args [] sigs outs) :
    Kleisli.mk (ofTypeMonad M) (Tuple m.Val args) ⟶
      Kleisli.mk (ofTypeMonad M) (Tuple m.Val outs) :=
  g.toTerm.denote m

/-- Observe the term arrow in the Kleisli category of partial values. -/
noncomputable def Term.denotePart (m : Model.{u, v, w} Op) (t : Term Op args [] sigs outs)
    (input : Tuple m.Val args) : _root_.Part (Tuple m.Val outs) :=
  (t.denote (M := _root_.Part) m).of input

/-- Observe the graph arrow in the Kleisli category of partial values. -/
noncomputable def Graph.denotePart (m : Model.{u, v, w} Op) (g : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) : _root_.Part (Tuple m.Val outs) :=
  (g.denote (M := _root_.Part) m).of input

end Silmaril.SSA.RVSDG.NestedTheta
