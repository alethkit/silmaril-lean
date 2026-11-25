module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Defs
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.DispatcherTransport

/-! # Outward continuations through a contextual dispatcher -/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop)
open CategoryTheory.CartesianMonoidalCategory (snd)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

/-- Moving a payload-only continuation into the outward arm of a contextual
iteration is categorical postcomposition. Feedback retains its original target
and payload. The continuation may have arbitrary effects. -/
theorem contextualLoop_mapDispatcherExit {E A B S : V}
    (body : J.obj (E ⊗ S) ⟶ J.obj (A ⨿ S)) (k : J.obj A ⟶ J.obj B) :
    contextualLoop J (body ≫ mapDispatcherExit J k) = contextualLoop J body ≫ k :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.contextualLoop_mapExit J body k

/-- A CFG's entry and feedback dispatcher can both run the continuation at
outward exits. This preserves the arrow obtained by running the original CFG
and then applying the same payload-only continuation. -/
theorem cfgDispatch_mapDispatcherExit {E A B S : V}
    (entry : J.obj E ⟶ J.obj (A ⨿ S))
    (body : J.obj (E ⊗ S) ⟶ J.obj (A ⨿ S)) (k : J.obj A ⟶ J.obj B) :
    caseWithContext J (entry ≫ mapDispatcherExit J k) (J.map (snd E B))
      (contextualLoop J (body ≫ mapDispatcherExit J k)) =
    caseWithContext J entry (J.map (snd E A)) (contextualLoop J body) ≫ k := by
  rw [contextualLoop_mapDispatcherExit,
    Proofs.SSA.Isotope.LambdaSSA.Rewrite.caseWithContext_mapExit]

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
