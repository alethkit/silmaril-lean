module

public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Categorical.Defs
public import Silmaril.SSA.RVSDG.Theta.Categorical.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Theta.Combinators

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Theta.Proofs

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory (fst snd lift toUnit)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (splitMapCoprod)

universe u v d h c k
variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]
variable {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D] [HasFiniteCoproducts D]

set_option backward.isDefEq.respectTransparency false

omit [HasFiniteCoproducts D] in
private theorem body_denote {A : τ} (m : Categorical.Model (Opcode Φ) D) (s : Step Φ A) :
    (body s).denote m = m.primitive (.step s) := by
  simp [body, Term.denote, Term.denoteOpen, Categorical.denoteShape, Categorical.extendScope,
    Categorical.readWires, Categorical.readOrigin, Categorical.project, Categorical.projectLocal,
    Categorical.appendScope, Categorical.appendLocal, Categorical.Model.locals,
    Categorical.portsObj, CartesianMonoidalCategory.leftUnitor_hom, Category.assoc]
  let X := m.value A
  let K := m.selectors.obj 2
  let R := X ⊗ 𝟙_ D
  let S := K ⊗ R
  let E := R ⊗ 𝟙_ D
  let f : R ⟶ S := m.primitive (.step s)
  let route : E ⟶ R := lift (fst R (𝟙_ D) ≫ fst X (𝟙_ D)) (toUnit E)
  let before : R ⟶ E := (ρ_ R).inv
  let value : R ⟶ S := before ≫ lift (𝟙 E) (route ≫ f) ≫ snd E S
  change lift (before ≫ lift (𝟙 E) (route ≫ f) ≫ snd E S ≫ fst K R)
    (lift (before ≫ lift (𝟙 E) (route ≫ f) ≫ snd E S ≫ snd K R ≫ fst X (𝟙_ D))
      (before ≫ toUnit E)) = f
  have hroute : route = fst R (𝟙_ D) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [route]
    · apply CategoryTheory.Limits.IsTerminal.hom_ext CartesianMonoidalCategory.isTerminalTensorUnit
  have hvalue : value = f := by
    simp [value, before, hroute]
  have hfst : before ≫ lift (𝟙 E) (route ≫ f) ≫ snd E S ≫ fst K R =
      value ≫ fst K R := by simp only [value, Category.assoc]
  have hsnd : before ≫ lift (𝟙 E) (route ≫ f) ≫ snd E S ≫ snd K R ≫ fst X (𝟙_ D) =
      value ≫ snd K R ≫ fst X (𝟙_ D) := by simp only [value, Category.assoc]
  rw [hfst, hsnd]
  rw [hvalue]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [CartesianMonoidalCategory.lift_fst]
    rfl
  · change lift (f ≫ fst K R)
      (lift (f ≫ snd K R ≫ fst X (𝟙_ D)) (before ≫ toUnit E)) ≫ snd K R = f ≫ snd K R
    rw [CartesianMonoidalCategory.lift_snd]
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · apply IsTerminal.hom_ext CartesianMonoidalCategory.isTerminalTensorUnit

variable {C : Type c} [Category.{k} C] [HasFiniteCoproducts C]
variable [SymmetricCategory D] [DistributiveTensor D] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C] [DistributivePremonoidalCategory C]
variable (J : D ⥤ C)

section Route

variable [DistributiveFreydCategory J]

private theorem project_route (sel : Categorical.Selectors D) (X : D) :
    J.map (encodeStep sel X) ≫ RVSDG.Theta.route J sel (X ⊗ 𝟙_ D) ≫
      coprod.map (J.map (ρ_ X).hom) (J.map (ρ_ X).hom) = splitMapCoprod J X X := by
  apply (cancel_epi (coprodComparison J X X)).1
  have left := RVSDG.Theta.route_leg J sel (X ⊗ 𝟙_ D) (0 : Fin 2)
  have right :
      J.map (Categorical.selectorLeg (sel.tag (1 : Fin 2)) :
        X ⊗ 𝟙_ D ⟶ sel.obj 2 ⊗ (X ⊗ 𝟙_ D)) ≫ RVSDG.Theta.route J sel (X ⊗ 𝟙_ D) =
        coprod.inr :=
    RVSDG.Theta.route_leg J sel (X ⊗ 𝟙_ D) (1 : Fin 2)
  apply coprod.hom_ext
  · simp only [coprodComparison, coprod.inl_desc_assoc, splitMapCoprod,
      IsIso.hom_inv_id, Category.comp_id]
    rw [← J.map_comp_assoc, encodeStep, coprod.inl_desc, J.map_comp, Category.assoc,
      ← Category.assoc (J.map (Categorical.selectorLeg (sel.tag (0 : Fin 2)))), left]
    simp [← J.map_comp_assoc]
  · simp only [coprodComparison, coprod.inr_desc_assoc, splitMapCoprod,
      IsIso.hom_inv_id, Category.comp_id]
    rw [← J.map_comp_assoc, encodeStep, coprod.inr_desc, J.map_comp, Category.assoc,
      ← Category.assoc (J.map (Categorical.selectorLeg (sel.tag (1 : Fin 2)))), right]
    simp [← J.map_comp_assoc]

end Route

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

theorem graph_projects (M : TypeModel τ D)
    (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f))
    (sel : Categorical.Selectors D) {A : τ} (s : Step Φ A) :
    (graph s).denote J (valueModel M prim sel) ≫ J.map (ρ_ (M.obj A)).hom =
      J.map (ρ_ (M.obj A)).hom ≫
        iterate (J.map (stepMap M prim s) ≫ splitMapCoprod J (M.obj A) (M.obj A)) := by
  let X := M.obj A
  let p := (ρ_ X).hom
  let mapped := J.map (stepMap M prim s) ≫ splitMapCoprod J X X
  let raw := RVSDG.Theta.step J (valueModel M prim sel)
    (J.map ((graph s).body.denote (valueModel M prim sel)))
  have sq : raw ≫ coprod.map (J.map p) (J.map p) = J.map p ≫ mapped := by
    unfold raw RVSDG.Theta.step graph
    rw [Term.denote_toGraph, body_denote]
    rw [Category.assoc]
    change J.map (p ≫ stepMap M prim s ≫ encodeStep sel X) ≫
      RVSDG.Theta.route J sel (X ⊗ 𝟙_ D) ≫ coprod.map (J.map p) (J.map p) = _
    simp only [J.map_comp, Category.assoc]
    rw [project_route]
  change iterate raw ≫ J.map p = J.map p ≫ iterate mapped
  rw [ElgotCategory.naturality]
  apply ElgotFreydCategory.pure_uniformity J _ _ p
  simpa only [Category.assoc, coprod.map_map, Category.comp_id, Category.id_comp] using sq

end Silmaril.SSA.RVSDG.LambdaSSA.Theta.Proofs
