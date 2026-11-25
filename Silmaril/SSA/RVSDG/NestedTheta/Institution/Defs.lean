module

public import Silmaril.SSA.RVSDG.Institution.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Defs

/-! # Equations for recursively nested γ and θ with ordered state -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution

open CategoryTheory Silmaril.Logic.Institution
open RVSDG.Institution (OpcodeMap)
open OrderedRuntime.Structured (Instruction Values Ty)

universe u v w
variable {V S : Type u} {P Q : Dialect.{u,v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

/-- Relabel opcodes while keeping every port, wire and numbered position. -/
def mapTerm (f : OpcodeMap P Q) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Term P args past sigs outs → Term Q args past sigs outs
  | _, _, _, _, .ret wires => .ret wires
  | _, _, _, _, .bind ⟨ins, .base (.simple op), inputs, childSigs⟩ children rest =>
    .bind ⟨ins, .base (.simple (f op)), inputs, childSigs⟩
      (fun i => mapTerm f (children i)) (mapTerm f rest)
  | _, _, _, _, .bind ⟨_, .base (.gamma extra), inputs, childSigs⟩ children rest =>
    .bind ⟨_, .base (.gamma extra), inputs, childSigs⟩
      (fun i => mapTerm f (children i)) (mapTerm f rest)
  | _, _, _, _, .bind ⟨_, .theta carried, inputs, childSigs⟩ children rest =>
    .bind ⟨_, .theta carried, inputs, childSigs⟩
      (fun i => mapTerm f (children i)) (mapTerm f rest)

def mapGraph (f : OpcodeMap P Q) (g : Graph P args past sigs outs) : Graph Q args past sigs outs :=
  (mapTerm f g.toTerm).toGraph

/-- Keep the value and snapshot carriers and precompose the primitive actions. -/
def monadicReduct {m : Type (max u w) → Type (max u w)} (f : OpcodeMap P Q)
    (model : MonadicModel.{u,v,w} Q m) : MonadicModel.{u,v,w} P m where
  value := model.value
  snapshot := model.snapshot
  primitive op := model.primitive (f op)

/-- A fixed alphabet of value sorts with distinct pure and effectful opcodes.
The implicit store is part of the model. Unit state ports are unchanged. -/
structure Signature (V : Type u) where
  pure : Dialect.{u,v} V PUnit.{u + 1}
  effect : Dialect.{u,v} V PUnit.{u + 1}

structure Signature.Hom (P Q : Signature.{u,v} V) where
  pure : OpcodeMap P.pure Q.pure
  effect : OpcodeMap P.effect Q.effect

instance : Category.{max u v} (Signature.{u,v} V) where
  Hom := Signature.Hom
  id _ := ⟨fun op => op, fun op => op⟩
  comp f g := ⟨fun op => g.pure (f.pure op), fun op => g.effect (f.effect op)⟩

abbrev Signature.op (P : Signature.{u,v} V) := Instruction P.pure P.effect

def Signature.opcodeMap {P Q : Signature.{u,v} V} (f : P ⟶ Q) : OpcodeMap P.op Q.op
  | _, _, .pure op => .pure (Signature.Hom.pure f op)
  | _, _, .effect op => .effect (Signature.Hom.effect f op)

/-- Models use total primitive state actions and the existing partial Elgot
interpretation for iteration. -/
abbrev Model (P : Signature.{u,v} V) (σ : Type (max u w)) :=
  OrderedRuntime.Structured.Model.{u,v,w} P.pure P.effect (StateM σ)

def reduct {P Q : Signature.{u,v} V} {σ : Type (max u w)} (f : P ⟶ Q)
    (model : Model.{u,v,w} Q σ) : Model.{u,v,w} P σ where
  value := model.value
  runPure op := model.runPure (Signature.Hom.pure f op)
  effect op := model.effect (Signature.Hom.effect f op)

structure Equation (P : Signature.{u,v} V) where
  args : Ports (Ty V)
  outs : Ports (Ty V)
  leftSigs : List (Ports (Ty V))
  rightSigs : List (Ports (Ty V))
  lhs : Graph P.op args [] leftSigs outs
  rhs : Graph P.op args [] rightSigs outs

def Equation.map {P Q : Signature.{u,v} V} (f : P ⟶ Q) (e : Equation P) : Equation Q :=
  ⟨e.args, e.outs, e.leftSigs, e.rightSigs, mapGraph (Signature.opcodeMap f) e.lhs,
    mapGraph (Signature.opcodeMap f) e.rhs⟩

/-- Compare full partial observations, including every returned port and the
final store, for every input tuple and initial store. -/
def Equation.Holds {P : Signature.{u,v} V} {σ : Type (max u w)} (e : Equation P)
    (model : Model.{u,v,w} P σ) : Prop :=
  ∀ (input : Tuple (Values model.value) e.args) (store : σ),
    OrderedState.observe model e.lhs input store = OrderedState.observe model e.rhs input store

def reductFunctor {P Q : Signature.{u,v} V} {σ : Type (max u w)} (f : P ⟶ Q) :
    Discrete (Model.{u,v,w} Q σ) ⥤ Discrete (Model.{u,v,w} P σ) :=
  Discrete.functor fun m => Discrete.mk (reduct f m)

def room (P : Signature.{u,v} V) (σ : Type (max u w)) :
    Room.{max u v, max (u + 1) v (w + 1), max (u + 1) v (w + 1)} where
  Sen := Equation P
  Mod := Cat.of (Discrete (Model.{u,v,w} P σ))
  Sat m e := e.Holds m.as

end Silmaril.SSA.RVSDG.NestedTheta.Institution
