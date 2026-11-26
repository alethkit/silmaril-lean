module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Reduct.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Sentence.Thms

/-! # Exact structured SSA signature maps on models and equations -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits

variable {τ ε : Type} [TypeFormers τ] {P Q : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

/-- Model reduct over a primitive relabelling, between the existing discrete
categories of coherent categorical models for the two signatures. -/
noncomputable def reductFunctor (g : P ⟶ Q) : (ssaRoom J Q).Mod ⥤ (ssaRoom J P).Mod :=
  ShrinkHoms.inverse.{0} (Discrete (CoherentRegionModel J Q)) ⋙
    Discrete.functor (fun K => Discrete.mk (K.reduct g)) ⋙
    ShrinkHoms.functor.{0} (Discrete (CoherentRegionModel J P))

/-- Satisfaction along a primitive map, using the exact LetCase algebra reduct. -/
theorem ssaSat_map_iff (g : P ⟶ Q) (K : CoherentRegionModel J Q) (e : SSAEquation P) :
    K.denoteSSA (mapEquation g e).2.1 = K.denoteSSA (mapEquation g e).2.2 ↔
      (K.reduct g).denoteSSA e.2.1 = (K.reduct g).denoteSSA e.2.2 := by
  rw [← sat_compile_iff K (mapEquation g e), ← sat_compile_iff (K.reduct g) e,
    compile_natural, K.caseAlgebra_reduct]
  exact LetCase.satisfaction Γ₀ g K.caseAlgebra (compile e)

/-- A primitive relabelling as a corridor of exact structured SSA equation rooms. -/
noncomputable def ssaCorridor (g : P ⟶ Q) : ssaRoom J P ⟶ ssaRoom J Q where
  sen := mapEquation g
  mod := reductFunctor g
  sat K e := ssaSat_map_iff g (ShrinkHoms.fromShrinkHoms K).as e

end Silmaril.Isotope.Institution.Acyclic
