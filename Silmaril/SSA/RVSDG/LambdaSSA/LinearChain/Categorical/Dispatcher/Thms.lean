module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Dispatcher.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Dispatch
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Context
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Iteration

/-! # Interpreting payload-only CFG blocks and grouping their feedback -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (snd)
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics.Categorical (ctxObj labelObj labelInject Denotes RegionDenotes)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

variable {n : Nat} {A X Y : τ} {Γ L : List τ}

omit [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] in
/-- Case on a computed sum when the selected continuation reads only its
payload. Both continuations can be effectful. -/
theorem case_project [DistributiveFreydCategory J] [FreydCategory.CentralUnit J] {E X Y T : V}
    (f : J.obj E ⟶ J.obj (X ⨿ Y)) (l : J.obj X ⟶ J.obj T) (r : J.obj Y ⟶ J.obj T) :
    Isotope.LetIter.ProofRelevant.Semantics.Categorical.caseWithContext J f
        (J.map (snd E X) ≫ l) (J.map (snd E Y) ≫ r) =
      f ≫ Isotope.LetIter.ProofRelevant.Semantics.Categorical.splitMapCoprod J X Y ≫ coprod.desc l r :=
  Proofs.case_project J f l r

theorem call_denotes (p : TwoBlock.Instruction Φ X Y) :
    Denotes J M (p.typing Γ) (J.map (snd (ctxObj M Γ) (M.obj X)) ≫ call J M p) :=
  Proofs.call_denotes J M p

theorem case_denotes [FreydCategory.CentralUnit J]
    (p : TwoBlock.Instruction Φ A (Silmaril.coprod X Y)) (left : Site L X) (right : Site L Y) :
    RegionDenotes J M
      (.case (p.typing Γ) (.br left.typing (.var (i := 0) rfl)) (.br right.typing (.var (i := 0) rfl)))
      (J.map (snd (ctxObj M Γ) (M.obj A)) ≫ caseArrow J M p left right) :=
  Proofs.case_denotes J M p left right

@[reassoc] theorem dispatch_at (R : Fin n → τ) {T : C}
    (f : ∀ i, J.obj (M.obj (R i)) ⟶ T) (i : Fin n) :
    J.map (Isotope.LambdaSSA.Semantics.Categorical.finiteLabelInject M R i) ≫ dispatch J M R f = f i :=
  Proofs.dispatch_at J M R f i

theorem local_ext (R : Fin n → τ) {T : C} {f g : J.obj (labelObj M (List.ofFn R)) ⟶ T}
    (eq : ∀ i, J.map (localInject M R i) ≫ f = J.map (localInject M R i) ≫ g) : f = g :=
  Proofs.local_ext J M R eq

theorem cfgStepOf_at (R : Fin n → τ) (L : List τ)
    (arrows : ∀ i, J.obj (M.obj (R i)) ⟶ J.obj (labelObj M (List.ofFn R ++ L))) (i : Fin n) :
    J.map (localInject M R i) ≫ cfgStepOf J M R L arrows = arrows i ≫ decodeLabels J M R L :=
  Proofs.cfgStepOf_at J M R L arrows i

theorem decode_local (R : Fin n → τ) (L : List τ) (i : Fin n) :
    J.map (siteArrow M (localSite R L i)) ≫ decodeLabels J M R L =
      J.map (localInject M R i) ≫ coprod.inr :=
  Proofs.decode_local J M R L i

theorem decode_exit (R : Fin n → τ) (L : List τ) (i : Fin L.length)
    (atExit : Isotope.SSA.At L i (L.get i)) :
    J.map (siteArrow M (externalSite R L i)) ≫ decodeLabels J M R L =
      J.map (labelInject M i atExit) ≫ coprod.inl :=
  Proofs.decode_exit J M R L i atExit

/-- An actual SSA CFG whose blocks read only their parameters denotes the
payload dispatcher entered at its chosen internal label. -/
theorem payload_cfg_denotes [FreydCategory.CentralUnit J] (R : Fin (n + 1) → τ) (i : Fin (n + 1))
    {entry : Region Φ} {blocks : Fin (n + 1) → Region Φ}
    (he : Region.HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ j, Region.HasType (R j :: Γ) (blocks j) (List.ofFn R ++ L))
    (fe : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (R i)))
    (de : RegionDenotes J M he (fe ≫ J.map (siteArrow M (localSite R L i))))
    (arrows : ∀ j, J.obj (M.obj (R j)) ⟶ J.obj (labelObj M (List.ofFn R ++ L)))
    (db : ∀ j, RegionDenotes J M (hb j)
      (J.map (snd (ctxObj M Γ) (M.obj (R j))) ≫ arrows j)) :
    RegionDenotes J M (.cfg R he hb)
      (fe ≫ J.map (localInject M R i) ≫ iterate (cfgStepOf J M R L arrows)) :=
  Proofs.payload_cfg_denotes J M R i he hb fe de arrows db

/-- Fuse two dispatchers and use a pure state injection to restrict the outer
feedback to one entry type. -/
theorem group_feedback {H I : V} {O : C} (enter : H ⟶ I)
    (inner : J.obj I ⟶ (O ⨿ J.obj I) ⨿ J.obj I)
    (round : J.obj H ⟶ O ⨿ J.obj H)
    (square : J.map enter ≫ iterate inner = round ≫ coprod.map (𝟙 O) (J.map enter)) :
    J.map enter ≫ iterate (inner ≫ coprod.desc (𝟙 (O ⨿ J.obj I)) coprod.inr) = iterate round :=
  Proofs.close_grouped J enter inner round square

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical
