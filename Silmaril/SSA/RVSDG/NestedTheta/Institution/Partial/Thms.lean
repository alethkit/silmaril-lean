module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Institution.Partial.Reindex

/-! # Satisfaction for the partial ordered nested dialect -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial

open CategoryTheory Silmaril.Logic.Institution
open OrderedRuntime.Structured (Values Ty)
open OrderedState.Partial (Abnormal observe abnormal)

universe u v w
variable {V : Type u} {A B C : Signature.{u,v} V} {σ : Type (max u w)}
variable {args outs : Ports (Ty V)} {sigs : List (Ports (Ty V))}

theorem observe_map (f : A ⟶ B) (m : Model.{u,v,w} B σ)
    (g : Graph A.base.op args [] sigs outs) (input : Tuple (Values m.value) args) (store : σ) :
    observe m (Institution.mapGraph (Signature.Hom.opcodeMap f) g) input store =
      observe (reduct f m) g input store :=
  Proofs.observe_map f m g input store

/-- The target's abnormal observations are exactly the relabelled source
observations in the reduct. In particular migration adds no blocked sites. -/
theorem abnormal_map (f : A ⟶ B) (m : Model.{u,v,w} B σ)
    (g : Graph A.base.op args [] sigs outs) (input : Tuple (Values m.value) args) (store : σ)
    (target : Abnormal B.base.effect m.value σ) :
    abnormal m (Institution.mapGraph (Signature.Hom.opcodeMap f) g) input store target ↔
      ∃ source, abnormal (reduct f m) g input store source ∧ mapAbnormal f source = target :=
  Proofs.abnormal_map f m g input store target

theorem abnormal_map_iff (f : A ⟶ B) (m : Model.{u,v,w} B σ)
    (g : Graph A.base.op args [] sigs outs) (input : Tuple (Values m.value) args) (store : σ)
    (source : Abnormal A.base.effect m.value σ) :
    abnormal m (Institution.mapGraph (Signature.Hom.opcodeMap f) g) input store (mapAbnormal f source) ↔
      abnormal (reduct f m) g input store source :=
  Proofs.abnormal_map_iff f m g input store source

theorem Equation.satisfaction (f : A ⟶ B) (e : Equation A) (m : Model.{u,v,w} B σ) :
    Equation.Holds (Equation.map f e) m ↔ Equation.Holds e (reduct f m) :=
  Proofs.satisfaction f e m

theorem Equation.map_id (e : Equation A) : Equation.map (𝟙 A) e = e :=
  Institution.Equation.map_id e

theorem Equation.map_comp (f : A ⟶ B) (g : B ⟶ C) (e : Equation A) :
    Equation.map (f ≫ g) e = Equation.map g (Equation.map f e) :=
  Institution.Equation.map_comp (Signature.Hom.forget f) (Signature.Hom.forget g) e

theorem reductFunctor_id (A : Signature.{u,v} V) :
    reductFunctor (σ := σ) (𝟙 A) = 𝟭 (Discrete (Model A σ)) :=
  Proofs.reductFunctor_id A

theorem reductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    reductFunctor (σ := σ) (f ≫ g) = reductFunctor g ⋙ reductFunctor f :=
  Proofs.reductFunctor_comp f g

@[expose] def corridor (f : A ⟶ B) : room A σ ⟶ room B σ :=
  ⟨Equation.map f, reductFunctor f, fun m e => Equation.satisfaction f e m.as⟩

theorem corridor_id (A : Signature.{u,v} V) : corridor (σ := σ) (𝟙 A) = 𝟙 (room A σ) :=
  Room.hom_ext (funext Equation.map_id) (reductFunctor_id A)

theorem corridor_comp (f : A ⟶ B) (g : B ⟶ C) :
    corridor (σ := σ) (f ≫ g) = corridor f ≫ corridor g :=
  Room.hom_ext (funext (Equation.map_comp f g)) (reductFunctor_comp f g)

@[expose] def inst (V : Type u) (σ : Type (max u w)) :
    Inst.{max u (v + 1), max u v, max u v, max (u + 1) v (w + 1), max (u + 1) v (w + 1)} where
  Sign := Signature.{u,v} V
  I := { obj := fun S => room S σ, map := corridor, map_id := corridor_id, map_comp := corridor_comp }

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial
