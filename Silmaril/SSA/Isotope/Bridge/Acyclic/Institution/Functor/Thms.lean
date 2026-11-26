module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Functor.Defs
public import Silmaril.Logic.Institution.Morphism
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Functor

/-! # The exact structured SSA institution over fixed types -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Inst Room)

variable {τ ε : Type} [TypeFormers τ] {P Q S : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

/-- The coherent model categories are discrete, so a model functor out of
one is determined by its action on objects. -/
theorem ssaModelFunctor_ext {D : Type*} [Category* D]
    {F G : (ssaRoom J P).Mod ⥤ D} (h : ∀ K, F.obj K = G.obj K) : F = G :=
  ssaModelFunctor_ext_proof h

@[simp] theorem ssaCorridor_id (P : InstrSig τ ε) :
    ssaCorridor (J := J) (𝟙 P) = 𝟙 (ssaRoom J P) :=
  ssaCorridor_id_proof P

@[simp] theorem ssaCorridor_comp (f : P ⟶ Q) (g : Q ⟶ S) :
    ssaCorridor (J := J) (f ≫ g) = ssaCorridor f ≫ ssaCorridor g :=
  ssaCorridor_comp_proof f g

/-- Exact single-exit structured SSA equations, with discrete categories of
coherent region models over a fixed strong Elgot Freyd functor. -/
noncomputable def ssaInst (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : InstrSig τ ε ⥤ Room.{0, 0, 1} where
  obj := ssaRoom J
  map g := ssaCorridor g
  map_id := ssaCorridor_id
  map_comp := ssaCorridor_comp

/-- The sentence reification and the algebra reduct commute with every
primitive signature map, as a square of corridors. -/
theorem reifyCorridor_natural (g : P ⟶ Q) :
    (LetCase.inst Γ₀).map g ≫ reifyCorridor J Q = reifyCorridor J P ≫ ssaCorridor g :=
  reifyCorridor_natural_proof g

/-- The existing LetCase institution for the empty named context, bundled over
the fixed-type primitive signature category. -/
def letCaseInstitution (τ ε : Type) [TypeFormers τ] : Inst.{1, 0, 0, 0, 1} :=
  ⟨InstrSig τ ε, LetCase.inst (Ctx.nil : Ctx Empty τ)⟩

/-- The bundled exact structured SSA institution. -/
noncomputable def ssaInstitution (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (τ ε : Type) [TypeFormers τ] : Inst.{1, 0, 0, 0, 1} :=
  ⟨InstrSig τ ε, ssaInst J⟩

/-- Reification is an institution comorphism over the identity on primitive
signatures. A coherent SSA model supplies the LetCase operation algebra. -/
noncomputable def reifyComorphism (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (τ ε : Type) [TypeFormers τ] :
    Inst.CoHom (letCaseInstitution τ ε) (ssaInstitution J τ ε) where
  Φ := 𝟭 (InstrSig τ ε)
  ρ := { app := reifyCorridor J, naturality := fun {_ _} g => reifyCorridor_natural g }

end Silmaril.Isotope.Institution.Acyclic
