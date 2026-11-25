module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Defs

/-! # Nested RVSDG equations observing block and divergence -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial

open CategoryTheory Silmaril.Logic.Institution
open OrderedRuntime.Structured (Values)
open OrderedState.Partial (Abnormal Block)

universe u v w
variable {V : Type u} {σ : Type (max u w)}

/-- A dialect over the same fixed ports and shared store as the total institution. -/
structure Signature (V : Type u) where
  base : Institution.Signature.{u,v} V

/-- A blocked opcode is observable. Thus the effect map must be injective
at each ordered port signature. Pure opcodes never report a block. -/
structure Signature.Hom (P Q : Signature.{u,v} V) where
  forget : P.base ⟶ Q.base
  effect_injective : ∀ ins outs, Function.Injective
    (Institution.Signature.Hom.effect forget (ins := ins) (outs := outs))

instance : Category.{max u v} (Signature.{u,v} V) where
  Hom := Signature.Hom
  id P := ⟨𝟙 P.base, fun _ _ => Function.injective_id⟩
  comp f g := ⟨f.forget ≫ g.forget, fun ins outs =>
    (g.effect_injective ins outs).comp (f.effect_injective ins outs)⟩

variable {A B C : Signature.{u,v} V}

abbrev Signature.Hom.opcodeMap (f : A ⟶ B) : RVSDG.Institution.OpcodeMap A.base.op B.base.op :=
  Institution.Signature.opcodeMap (Signature.Hom.forget f)

abbrev Equation (A : Signature.{u,v} V) := Institution.Equation A.base

abbrev Model (A : Signature.{u,v} V) (σ : Type (max u w)) :=
  OrderedState.Partial.Model.{u,v,w} A.base.pure A.base.effect σ

def reduct (f : A ⟶ B) (m : Model.{u,v,w} B σ) : Model.{u,v,w} A σ where
  value := m.value
  runPure op := m.runPure (Institution.Signature.Hom.pure (Signature.Hom.forget f) op)
  effect op := m.effect (Institution.Signature.Hom.effect (Signature.Hom.forget f) op)

def mapBlock (f : A ⟶ B) {value : V → Type (max u w)} (b : Block A.base.effect value σ) :
    Block B.base.effect value σ :=
  ⟨b.path, b.vertex, b.ins, b.outs, Institution.Signature.Hom.effect (Signature.Hom.forget f) b.opcode,
    b.input, b.store⟩

/-- Numbering, child choice, inputs and attempt store are unchanged. -/
def mapAbnormal (f : A ⟶ B) {value : V → Type (max u w)} :
    Abnormal A.base.effect value σ → Abnormal B.base.effect value σ
  | .blocked b => .blocked (mapBlock f b)
  | .diverges => .diverges

def Equation.map (f : A ⟶ B) (e : Equation A) : Equation B :=
  Institution.Equation.map (Signature.Hom.forget f) e

/-- Compare finite returns with their full tuple and store, block diagnostics
with all their fields, and the existence of a productive infinite run. -/
def Equation.Holds (e : Equation A) (m : Model.{u,v,w} A σ) : Prop :=
  ∀ (input : Tuple (Values m.value) e.args) (store : σ),
    OrderedState.Partial.observe m e.lhs input store =
      OrderedState.Partial.observe m e.rhs input store ∧
    ∀ obs, OrderedState.Partial.abnormal m e.lhs input store obs ↔
      OrderedState.Partial.abnormal m e.rhs input store obs

def reductFunctor (f : A ⟶ B) : Discrete (Model.{u,v,w} B σ) ⥤ Discrete (Model.{u,v,w} A σ) :=
  Discrete.functor fun m => Discrete.mk (reduct f m)

def room (A : Signature.{u,v} V) (σ : Type (max u w)) :
    Room.{max u v, max (u + 1) v (w + 1), max (u + 1) v (w + 1)} where
  Sen := Equation A
  Mod := Cat.of (Discrete (Model.{u,v,w} A σ))
  Sat m e := Equation.Holds e m.as

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial
