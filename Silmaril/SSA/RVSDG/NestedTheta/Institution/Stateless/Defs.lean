module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Defs

/-! # Stateless nested RVSDG equations over a fixed value alphabet -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless

open CategoryTheory Silmaril.Logic.Institution
open OrderedRuntime.Structured (Data Values Ty Instruction)
open RVSDG.Institution (OpcodeMap)

universe u v w
variable {V : Type u}

abbrev NoEffect (V : Type u) : Dialect.{u,v} V PUnit.{u+1} := fun _ _ => PEmpty

/-- Primitive declarations use only value and selector ports. -/
structure Signature (V : Type u) where
  pure : Dialect.{u,v} V PUnit.{u+1}
  ports : ∀ {ins outs}, pure ins outs → Data ins ∧ Data outs

def Signature.ordered (A : Signature.{u,v} V) : Institution.Partial.Signature.{u,v} V :=
  ⟨⟨A.pure, NoEffect V⟩⟩

/-- Use the ordered institution's port-preserving homs between empty-effect
signatures. The effect component has empty domain. -/
instance : Category.{max u v} (Signature.{u,v} V) where
  Hom A B := A.ordered ⟶ B.ordered
  id A := 𝟙 A.ordered
  comp {X Y Z} f g := (show X.ordered ⟶ Y.ordered from f) ≫ (show Y.ordered ⟶ Z.ordered from g)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable {A B : Signature.{u,v} V}

def Signature.rename (f : OpcodeMap A.pure B.pure) : A ⟶ B :=
  ⟨⟨f, fun op => nomatch op⟩, fun _ _ op => nomatch op⟩

def signatureInclusion (V : Type u) : Signature.{u,v} V ⥤ Institution.Partial.Signature.{u,v} V where
  obj := Signature.ordered
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev Signature.op (A : Signature.{u,v} V) := A.ordered.base.op

/-- Every region boundary and binding has data ports only. The fixed
unit sort in the ambient port alphabet never appears as a state port. -/
def NoState {Q : Dialect.{u,v} V PUnit.{u+1}} :
    {args outs : Ports (Ty V)} → {past sigs : List (Ports (Ty V))} → Term Q args past sigs outs → Prop
  | args, outs, _, _, .ret _ => Data args ∧ Data outs
  | _, _, _, head :: _, .bind node children rest =>
    Data node.ins ∧ Data head ∧ (∀ i, NoState (children i)) ∧ NoState rest

/-- A stateless equation is literally an empty-effect ordered equation
whose numbered graphs have state-free ports. -/
abbrev Equation (A : Signature.{u,v} V) :=
  { e : Institution.Partial.Equation A.ordered // NoState e.lhs.toTerm ∧ NoState e.rhs.toTerm }

/-- A model has only value carriers and total primitive interpretations. -/
structure Model (A : Signature.{u,v} V) where
  value : V → Type (max u w)
  run {ins outs : Ports (Ty V)} :
    A.pure ins outs → Tuple (Values value) ins → Tuple (Values value) outs

def Model.partial (m : Model.{u,v,w} A) : NestedTheta.Partial.Model.{u,v,max u w} A.op where
  value := m.value
  snapshot _ := PUnit
  primitive
    | .pure op, args => Part.some (m.run op args)
    | .effect op, _ => nomatch op

variable {args outs : Ports (Ty V)} {sigs : List (Ports (Ty V))}

noncomputable def observe (m : Model.{u,v,w} A) (g : Graph A.op args [] sigs outs)
    (input : Tuple (Values m.value) args) : Part (Tuple (Values m.value) outs) :=
  NestedTheta.Partial.observe m.partial g input

/-- With total primitives, absence of a finite return corresponds to
productive divergence. The inclusion proves this using ordered endpoints. -/
def Diverges (m : Model.{u,v,w} A) (g : Graph A.op args [] sigs outs)
    (input : Tuple (Values m.value) args) : Prop :=
  ¬ (observe m g input).Dom

def Equation.Holds (e : Equation A) (m : Model.{u,v,w} A) : Prop :=
  ∀ input : Tuple (Values m.value) e.val.args, observe m e.val.lhs input = observe m e.val.rhs input

def reduct (f : A ⟶ B) (m : Model.{u,v,w} B) : Model.{u,v,w} A where
  value := m.value
  run op := m.run (Institution.Signature.Hom.pure (Institution.Partial.Signature.Hom.forget f) op)

variable {σ : Type (max u w)}

def forgetStore (m : Institution.Partial.Model.{u,v,w} A.ordered σ) : Model.{u,v,w} A :=
  ⟨m.value, m.runPure⟩

def expand (m : Model.{u,v,w} A) : Institution.Partial.Model.{u,v,w} A.ordered σ where
  value := m.value
  runPure := m.run
  effect op := nomatch op

def reductFunctor (f : A ⟶ B) : Discrete (Model.{u,v,w} B) ⥤ Discrete (Model.{u,v,w} A) :=
  Discrete.functor fun m => Discrete.mk (reduct f m)

def forgetFunctor (A : Signature.{u,v} V) (σ : Type (max u w)) :
    Discrete (Institution.Partial.Model.{u,v,w} A.ordered σ) ⥤ Discrete (Model.{u,v,w} A) :=
  Discrete.functor fun m => Discrete.mk (forgetStore m)

def room (A : Signature.{u,v} V) :
    Room.{max u v, max (u + 1) v (w + 1), max (u + 1) v (w + 1)} where
  Sen := Equation A
  Mod := Cat.of (Discrete (Model.{u,v,w} A))
  Sat m e := e.Holds m.as

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless
