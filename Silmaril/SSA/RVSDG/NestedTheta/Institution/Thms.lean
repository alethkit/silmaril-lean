module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Institution.Reindex

/-! # The satisfaction condition for ordered nested RVSDG -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution

open CategoryTheory Silmaril.Logic.Institution
open RVSDG.Institution (OpcodeMap)
open OrderedRuntime.Structured (Values Ty)
open Silmaril.Elgot (Iterate)

universe u v w
variable {V S : Type u} {P Q R : Dialect.{u,v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

theorem mapGraph_id (g : Graph P args past sigs outs) : mapGraph (fun op => op) g = g :=
  Proofs.mapGraph_id g

theorem mapGraph_comp (f : OpcodeMap P Q) (g : OpcodeMap Q R) (t : Graph P args past sigs outs) :
    mapGraph (fun op => g (f op)) t = mapGraph g (mapGraph f t) :=
  Proofs.mapGraph_comp f g t

/-- The nested open interpretation commutes with replacing primitive denotations
by their images in the target dialect. -/
theorem denoteOpen_map {m : Type (max u w) → Type (max u w)} [Monad m] [Iterate m]
    (f : OpcodeMap P Q) (model : MonadicModel.{u,v,w} Q m) (t : Term P args past sigs outs)
    (input : Tuple model.Val args) (locals : Locals model.Val past) :
    (mapTerm f t).denoteOpenWith model input locals = t.denoteOpenWith (monadicReduct f model) input locals :=
  Proofs.denoteOpen_map f model t input locals

variable {A B C : Signature.{u,v} V} {σ : Type (max u w)}

theorem observe_map {args outs : Ports (Ty V)} {sigs : List (Ports (Ty V))}
    (f : A ⟶ B) (model : Model.{u,v,w} B σ) (g : Graph A.op args [] sigs outs)
    (input : Tuple (Values model.value) args) (store : σ) :
    OrderedState.observe model (mapGraph (Signature.opcodeMap f) g) input store =
      OrderedState.observe (reduct f model) g input store :=
  Proofs.observe_map f model g input store

theorem Equation.satisfaction (f : A ⟶ B) (e : Equation A) (model : Model.{u,v,w} B σ) :
    (e.map f).Holds model ↔ e.Holds (reduct f model) := by
  simp only [Equation.Holds, Equation.map, observe_map]
  rfl

/-- Satisfaction compares the unbounded finite derivations for each input
and initial store, at every returned tuple and final store. -/
theorem Equation.holds_iff_finite (e : Equation A) (model : Model.{u,v,w} A σ) :
    e.Holds model ↔ ∀ (input : Tuple (Values model.value) e.args) (initial : σ)
      (output : OrderedState.Configuration model.value σ e.outs),
      OrderedState.exec model e.lhs.toTerm input PUnit.unit initial output ↔
        OrderedState.exec model e.rhs.toTerm input PUnit.unit initial output :=
  Proofs.holds_iff_finite e model

theorem Equation.map_id (e : Equation A) : e.map (𝟙 A) = e :=
  Proofs.equation_map_id e

theorem Equation.map_comp (f : A ⟶ B) (g : B ⟶ C) (e : Equation A) :
    e.map (f ≫ g) = (e.map f).map g :=
  Proofs.equation_map_comp f g e

theorem reductFunctor_id (A : Signature.{u,v} V) :
    reductFunctor (σ := σ) (𝟙 A) = 𝟭 (Discrete (Model A σ)) :=
  Proofs.reductFunctor_id A

theorem reductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    reductFunctor (σ := σ) (f ≫ g) = reductFunctor g ⋙ reductFunctor f :=
  Proofs.reductFunctor_comp f g

@[expose] def corridor (f : A ⟶ B) : room A σ ⟶ room B σ :=
  ⟨Equation.map f, reductFunctor f, fun model e => e.satisfaction f model.as⟩

theorem corridor_id (A : Signature.{u,v} V) : corridor (σ := σ) (𝟙 A) = 𝟙 (room A σ) :=
  Room.hom_ext (funext Equation.map_id) (reductFunctor_id A)

theorem corridor_comp (f : A ⟶ B) (g : B ⟶ C) :
    corridor (σ := σ) (f ≫ g) = corridor f ≫ corridor g :=
  Room.hom_ext (funext (Equation.map_comp f g)) (reductFunctor_comp f g)

@[expose] def inst (V : Type u) (σ : Type (max u w)) :
    Inst.{max u (v + 1), max u v, max u v, max (u + 1) v (w + 1), max (u + 1) v (w + 1)} where
  Sign := Signature.{u,v} V
  I :=
    { obj := fun S => room S σ
      map := corridor
      map_id := corridor_id
      map_comp := corridor_comp }

end Silmaril.SSA.RVSDG.NestedTheta.Institution
