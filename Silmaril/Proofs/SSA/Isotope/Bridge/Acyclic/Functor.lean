module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Functor.Defs

/-! # Functoriality of exact SSA equations and coherent model reducts -/

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room)

private theorem functor_ext_from_discrete {M D : Type*} [Category* M] [IsDiscrete M]
    [Category* D] {F G : M ⥤ D} (h : ∀ K, F.obj K = G.obj K) : F = G := by
  refine Functor.ext_of_iso (NatIso.ofComponents (fun K => eqToIso (h K)) ?_) h (fun _ => rfl)
  intro K L f
  obtain rfl := obj_ext_of_isDiscrete f
  have hf : f = 𝟙 K := Subsingleton.elim _ _
  subst f
  simp

variable {τ ε : Type} [TypeFormers τ] {P Q S : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

private instance (P : InstrSig τ ε) : IsDiscrete (ssaRoom J P).Mod where
  subsingleton _ _ :=
    (ShrinkHoms.inverse.{0} (Discrete (CoherentRegionModel J P))).map_injective.subsingleton
  eq_of_hom f :=
    congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk)
      (Discrete.eq_of_hom ((ShrinkHoms.inverse.{0} (Discrete (CoherentRegionModel J P))).map f))

theorem ssaCorridor_id_proof (P : InstrSig τ ε) :
    ssaCorridor (J := J) (𝟙 P) = 𝟙 (ssaRoom J P) := by
  refine Room.hom_ext (funext mapEquation_id) ?_
  refine functor_ext_from_discrete fun K => ?_
  exact congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk)
    (CoherentRegionModel.reduct_id K.fromShrinkHoms.as)

theorem ssaCorridor_comp_proof (f : P ⟶ Q) (g : Q ⟶ S) :
    ssaCorridor (J := J) (f ≫ g) = ssaCorridor f ≫ ssaCorridor g := by
  refine Room.hom_ext (funext (mapEquation_comp f g)) ?_
  refine functor_ext_from_discrete fun K => ?_
  exact congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk)
    (CoherentRegionModel.reduct_comp f g K.fromShrinkHoms.as)

theorem reifyCorridor_natural_proof (g : P ⟶ Q) :
    (LetCase.inst Γ₀).map g ≫ reifyCorridor J Q = reifyCorridor J P ≫ ssaCorridor g := by
  refine Room.hom_ext (funext (reify_natural g)) ?_
  refine functor_ext_from_discrete fun K => ?_
  exact (K.fromShrinkHoms.as.caseAlgebra_reduct g).symm

end Silmaril.Isotope.Institution.Acyclic
