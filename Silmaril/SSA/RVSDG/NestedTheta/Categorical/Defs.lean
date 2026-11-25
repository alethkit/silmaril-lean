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

/-- The value interface and Kleisli arrows for the primitive generators. -/
structure MonadicModel (Op : Dialect.{u, v} V S) (M : Type (max u w) → Type (max u w)) where
  value : V → Type w
  snapshot : S → Type w
  primitive {ins outs : Ports (PortType V S)} : Op ins outs →
    Tuple (PortType.Val value snapshot) ins → M (Tuple (PortType.Val value snapshot) outs)

abbrev MonadicModel.Val (m : MonadicModel Op M) := PortType.Val m.value m.snapshot

/-- Embed a total value model into the computation category. -/
def MonadicModel.ofRuntime (m : Model.{u, v, w} Op) : MonadicModel Op M where
  value := m.value
  snapshot := m.state
  primitive op input := pure (m.run op input)

/-- Tag zero returns the payload, while tag one feeds it back. -/
def routeValue {value : V → Type w} {snapshot : S → Type w} :
    Tuple (PortType.Val value snapshot) (Theta.BodyResults carried) →
      Tuple (PortType.Val value snapshot) carried ⊕ Tuple (PortType.Val value snapshot) carried
  | .cons tag payload => Fin.cases (.inl payload) (fun _ => .inr payload) tag.down

def route (m : Model.{u, v, w} Op)
    (result : Tuple m.Val (Theta.BodyResults carried)) :
    Tuple m.Val carried ⊕ Tuple m.Val carried :=
  routeValue result

/-- Route the result of a complete body computation. A partial body may itself contain loops. -/
def stepWith {value : V → Type w} {snapshot : S → Type w}
    (body : Tuple (PortType.Val value snapshot) carried →
      M (Tuple (PortType.Val value snapshot) (Theta.BodyResults carried))) :
    Tuple (PortType.Val value snapshot) carried →
      M (Tuple (PortType.Val value snapshot) carried ⊕ Tuple (PortType.Val value snapshot) carried) :=
  body >=> fun result => pure (routeValue result)

def step (m : Model.{u, v, w} Op)
    (body : Tuple m.Val carried → M (Tuple m.Val (Theta.BodyResults carried))) :
    Tuple m.Val carried → M (Tuple m.Val carried ⊕ Tuple m.Val carried) :=
  stepWith body

/-- Present the routed step at the chosen Kleisli coproduct. -/
noncomputable def stepArrow [LawfulMonad M] (m : Model.{u, v, w} Op)
    (body : Tuple m.Val carried → M (Tuple m.Val (Theta.BodyResults carried))) :
    Kleisli.mk (ofTypeMonad M) (Tuple m.Val carried) ⟶
      Kleisli.mk (ofTypeMonad M) (Tuple m.Val carried) ⨿
      Kleisli.mk (ofTypeMonad M) (Tuple m.Val carried) :=
  Kleisli.Hom.mk (↾(step (M := M) m body)) ≫ (Kleisli.Type.coprodIsoSum M _ _).inv

variable [Iterate M]

/-- A primitive uses its assigned arrow, γ copairs its arms and θ iterates
the computation of its sole child in the computation category. -/
def Kind.denoteWith (m : MonadicModel Op M) :
    {ins outs : Ports (PortType V S)} → (kind : Kind Op ins outs) →
    (Fin kind.arity → Tuple m.Val kind.entry → M (Tuple m.Val kind.exit)) →
    Tuple m.Val ins → M (Tuple m.Val outs)
  | _, _, .base (.simple opcode), _, input => m.primitive opcode input
  | _, _, .base (.gamma _), arms, .cons tag payload => arms tag.down payload
  | _, _, .theta _, children, input => iter (stepWith (children (0 : Fin 1))) input

def Kind.denote (m : Model.{u, v, w} Op) (kind : Kind Op ins outs)
    (children : Fin kind.arity → Tuple m.Val kind.entry → M (Tuple m.Val kind.exit)) :
    Tuple m.Val ins → M (Tuple m.Val outs) :=
  kind.denoteWith (MonadicModel.ofRuntime m) children

/-- A let retains its pure scope, runs the node once, and appends its result.
Child calls receive only the node's declared entry tuple. -/
def Term.denoteOpenWith (m : MonadicModel Op M) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Term Op args past sigs outs → Tuple m.Val args → Locals m.Val past → M (Tuple m.Val outs)
  | _, _, _, _, .ret results, entry, locals => pure (results.read entry locals)
  | _, _, _, _, .bind node children rest, entry, locals => do
    let result ← node.kind.denoteWith m
      (fun i input => (children i).denoteOpenWith m input PUnit.unit) (node.inputs.read entry locals)
    rest.denoteOpenWith m entry (locals.snoc result)

def Term.denoteOpen (m : Model.{u, v, w} Op) (t : Term Op args past sigs outs) :
    Tuple m.Val args → Locals m.Val past → M (Tuple m.Val outs) :=
  t.denoteOpenWith (MonadicModel.ofRuntime m)

/-- Closed entry and exit tuples determine the source and target Kleisli objects. -/
def Term.denoteWith [LawfulMonad M] (m : MonadicModel Op M) (t : Term Op args [] sigs outs) :
    Kleisli.mk (ofTypeMonad M) (Tuple m.Val args) ⟶
      Kleisli.mk (ofTypeMonad M) (Tuple m.Val outs) :=
  Kleisli.Hom.mk (↾fun input => t.denoteOpenWith (M := M) m input PUnit.unit)

def Term.denote [LawfulMonad M] (m : Model.{u, v, w} Op) (t : Term Op args [] sigs outs) :
    Kleisli.mk (ofTypeMonad M) (Tuple m.Val args) ⟶
      Kleisli.mk (ofTypeMonad M) (Tuple m.Val outs) :=
  t.denoteWith (MonadicModel.ofRuntime m)

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
