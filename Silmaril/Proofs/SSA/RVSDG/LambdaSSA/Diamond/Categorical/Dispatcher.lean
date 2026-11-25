module

public import Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Dispatcher.Thms

/-! # The typed block dispatcher of the diamond CFG -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical.Proofs

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (snd)
open scoped MonoidalCategory
open Isotope.LambdaSSA (Tm)
open Isotope.LambdaSSA.Semantics.Categorical (ctxObj labelObj Denotes RegionDenotes)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LinearChain (localSite externalSite)
open LinearChain.Categorical (call choice siteArrow caseArrow call_denotes case_denotes
  cfgStepOf localInject payload_cfg_denotes)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

variable {A B X Y K E D : τ}

/-- Each CFG edge receives exactly its source's payload. Changing the result
of the dispatcher amounts to postcomposing these seven continuations. -/
structure Edges (A B X Y K E D : τ) (T : C) where
  exitHeader : J.obj (M.obj E) ⟶ T
  enterBody : J.obj (M.obj B) ⟶ T
  enterLeft : J.obj (M.obj X) ⟶ T
  enterRight : J.obj (M.obj Y) ⟶ T
  enterJoin : J.obj (M.obj K) ⟶ T
  exitJoin : J.obj (M.obj D) ⟶ T
  restart : J.obj (M.obj A) ⟶ T

def Edges.post {T U : C} (e : Edges J M A B X Y K E D T) (k : T ⟶ U) :
    Edges J M A B X Y K E D U :=
  ⟨e.exitHeader ≫ k, e.enterBody ≫ k, e.enterLeft ≫ k, e.enterRight ≫ k, e.enterJoin ≫ k,
    e.exitJoin ≫ k, e.restart ≫ k⟩

/-- Interpret every real block with the specified edge continuations. -/
noncomputable def arrows {T : C} (s : Blocks Φ A B X Y K E D) (e : Edges J M A B X Y K E D T) :
    ∀ i : Fin 5, J.obj (M.obj (localTypes A B X Y K i)) ⟶ T :=
  Fin.cases (motive := fun i => J.obj (M.obj (localTypes A B X Y K i)) ⟶ T)
    (choice J M s.header ≫ coprod.desc e.exitHeader e.enterBody)
    (Fin.cases (choice J M s.diamond.classifier ≫ coprod.desc e.enterLeft e.enterRight)
      (Fin.cases (call J M s.diamond.left ≫ e.enterJoin)
        (Fin.cases (call J M s.diamond.right ≫ e.enterJoin)
          (fun q => by
            obtain rfl := Fin.eq_zero q
            exact choice J M s.join ≫ coprod.desc e.exitJoin e.restart))))

theorem arrows_post {T U : C} (s : Blocks Φ A B X Y K E D)
    (e : Edges J M A B X Y K E D T) (f : T ⟶ U) (i : Fin 5) :
    arrows J M s e i ≫ f = arrows J M s (e.post J M f) i := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => Fin.cases ?_
    (fun k => Fin.cases ?_ (fun q => ?_) k) j) i) i
  · change (choice J M s.header ≫ coprod.desc e.exitHeader e.enterBody) ≫ f = _
    rw [Category.assoc, coprod.desc_comp]
    rfl
  · change (choice J M s.diamond.classifier ≫ coprod.desc e.enterLeft e.enterRight) ≫ f = _
    rw [Category.assoc, coprod.desc_comp]
    rfl
  · exact Category.assoc (call J M s.diamond.left) e.enterJoin f
  · exact Category.assoc (call J M s.diamond.right) e.enterJoin f
  · obtain rfl := Fin.eq_zero q
    change (choice J M s.join ≫ coprod.desc e.exitJoin e.restart) ≫ f = _
    rw [Category.assoc, coprod.desc_comp]
    rfl

noncomputable def labelEdges :
    Edges J M A B X Y K E D (J.obj (labelObj M (List.ofFn (localTypes A B X Y K) ++ [E,D]))) :=
  let R := localTypes A B X Y K
  ⟨J.map (siteArrow M (externalSite R [E,D] 0)), J.map (siteArrow M (localSite R [E,D] 1)),
    J.map (siteArrow M (localSite R [E,D] 2)), J.map (siteArrow M (localSite R [E,D] 3)),
    J.map (siteArrow M (localSite R [E,D] 4)), J.map (siteArrow M (externalSite R [E,D] 1)),
    J.map (siteArrow M (localSite R [E,D] 0))⟩

variable [FreydCategory.CentralUnit J]

private theorem blocks_denote (s : Blocks Φ A B X Y K E D) (i : Fin 5) :
    RegionDenotes J M (blockTyping s i)
      (J.map (snd (ctxObj M [A]) (M.obj (localTypes A B X Y K i))) ≫
        arrows J M s (labelEdges J M) i) := by
  let R := localTypes A B X Y K
  let hub := localSite R [E,D] 4
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => Fin.cases ?_
    (fun k => Fin.cases ?_ (fun q => ?_) k) j) i) i
  · exact case_denotes J M (Γ := [A]) s.header (externalSite R [E,D] 0) (localSite R [E,D] 1)
  · exact case_denotes J M (Γ := [A]) s.diamond.classifier (localSite R [E,D] 2) (localSite R [E,D] 3)
  · have h := RegionDenotes.br (h := hub.typing) (call_denotes J M (Γ := [A]) s.diamond.left)
    rw [Category.assoc] at h
    exact h
  · have h := RegionDenotes.br (h := hub.typing) (call_denotes J M (Γ := [A]) s.diamond.right)
    rw [Category.assoc] at h
    exact h
  · obtain rfl := Fin.eq_zero q
    exact case_denotes J M (Γ := [A]) s.join (externalSite R [E,D] 1) (localSite R [E,D] 0)

theorem cfg_denotes (s : Blocks Φ A B X Y K E D) :
    RegionDenotes J M (regionTyping s)
      (J.map (snd (𝟙_ V) (M.obj A)) ≫ J.map (localInject M (localTypes A B X Y K) 0) ≫
        iterate (cfgStepOf J M (localTypes A B X Y K) [E,D] (arrows J M s (labelEdges J M)))) := by
  let R := localTypes A B X Y K
  have var : Denotes J M (Tm.HasType.var (Φ := Φ) (Γ := [A]) (i := 0) rfl)
      (J.map (snd (𝟙_ V) (M.obj A))) := .var (i := 0) rfl
  exact payload_cfg_denotes J M R 0 _ (blockTyping s) _
    (RegionDenotes.br (h := (localSite R [E,D] 0).typing) var)
    (arrows J M s (labelEdges J M)) (blocks_denote J M s)

end Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical.Proofs
