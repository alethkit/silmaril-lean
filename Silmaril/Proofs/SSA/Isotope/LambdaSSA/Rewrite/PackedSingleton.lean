module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.PackedLabels

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
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

set_option backward.isDefEq.respectTransparency false in
theorem denoteSingletonRegion_br {a : Tm Φ} {f : J.obj (ctxObj M [A]) ⟶ J.obj (M.obj B)}
    {ha : Tm.HasType [A] a B} (d : Denotes J M ha f) :
    denoteSingletonRegion J M (.br (rfl : At [B] 0 B) ha) =
      J.map ((λ_ (M.obj A)).inv : M.obj A ⟶ ctxObj M [A]) ≫ f := by
  unfold denoteSingletonRegion
  rw [← (RegionDenotes.br (h := (rfl : At [B] 0 B)) d).eq_denote]
  simp only [Category.assoc, ← J.map_comp, labelInject_singletonLabelPayload, J.map_id,
    Category.comp_id]

theorem denoteSingletonRegion_forward :
    denoteSingletonRegion J M
      (.br (rfl : At [A] 0 A) (.var rfl) : Region.HasType [A] (.br 0 (.var 0) : Region Φ) [A]) =
      𝟙 (J.obj (M.obj A)) := by
  rw [denoteSingletonRegion_br J M (Denotes.var (J := J) (M := M) (rfl : At [A] 0 A))]
  change J.map (λ_ (M.obj A)).inv ≫ J.map (CartesianMonoidalCategory.snd _ _) = _
  rw [← CartesianMonoidalCategory.leftUnitor_hom, ← J.map_comp, Iso.inv_hom_id, J.map_id]

theorem denoteSingletonRegion_cfgZero {entry : Region Φ}
    (he : Region.HasType [A] entry [B]) (blocks : Fin 0 → Region Φ) :
    denoteSingletonRegion J M (.cfg Fin.elim0 he (fun i => i.elim0) :
      Region.HasType [A] (.cfg entry 0 blocks) [B]) = denoteSingletonRegion J M he := by
  unfold denoteSingletonRegion
  rw [← (RegionDenotes.cfgZero (R := Fin.elim0) he (blocks := blocks)
    (fun i => i.elim0) (denoteRegion_spec J M he)).eq_denote]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
