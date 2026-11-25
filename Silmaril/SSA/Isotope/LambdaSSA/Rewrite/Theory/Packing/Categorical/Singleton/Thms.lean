module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.PackedSingleton

/-! # Singleton denotation equations for branches and empty CFGs -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M] {A B : τ}

/-- A singleton branch denotes its payload, with only the input unitor left to account for. -/
theorem denoteSingletonRegion_br {a : Tm Φ} {f : J.obj (ctxObj M [A]) ⟶ J.obj (M.obj B)}
    {ha : Tm.HasType [A] a B} (d : Denotes J M ha f) :
    denoteSingletonRegion J M (.br (rfl : At [B] 0 B) ha) =
      J.map ((λ_ (M.obj A)).inv : M.obj A ⟶ ctxObj M [A]) ≫ f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.denoteSingletonRegion_br J M d

/-- Forwarding the input to the sole exit denotes the identity. -/
theorem denoteSingletonRegion_forward :
    denoteSingletonRegion J M
      (.br (rfl : At [A] 0 A) (.var rfl) : Region.HasType [A] (.br 0 (.var 0) : Region Φ) [A]) =
      𝟙 (J.obj (M.obj A)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.denoteSingletonRegion_forward J M

/-- A CFG with no blocks has the singleton denotation of its entry. -/
theorem denoteSingletonRegion_cfgZero {entry : Region Φ}
    (he : Region.HasType [A] entry [B]) (blocks : Fin 0 → Region Φ) :
    denoteSingletonRegion J M (.cfg Fin.elim0 he (fun i => i.elim0) :
      Region.HasType [A] (.cfg entry 0 blocks) [B]) = denoteSingletonRegion J M he :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.denoteSingletonRegion_cfgZero J M he blocks

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
