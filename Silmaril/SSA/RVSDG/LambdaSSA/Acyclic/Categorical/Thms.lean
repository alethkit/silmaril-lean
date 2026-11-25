module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Dispatcher.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Fold
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Dispatcher

/-! # Acyclic typed CFGs and nested γ agree at the join -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (snd)
open Isotope.LambdaSSA.Semantics.Categorical
  (ctxObj labelInject RegionDenotes RegionTypingCoherent denoteRegion singletonLabelPayload)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LinearChain (Site)

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

variable {A B : τ} {L : List τ} {T : C}

section Distributive
variable (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- The forward block equations implement the body at an arbitrary existing
join, even if the other existing labels have unrelated interpretations. -/
theorem compile_fold (b : Body Φ A B) (join : Site L B)
    (arrows : LabelArrows J M (b.compile join).labels T)
    (solve : Solves J M (b.compile join).code arrows) :
    arrows A (b.compile join).entry =
      denoteForm J M (.body b) ≫ arrows B ((b.compile join).code.lift join) :=
  Proofs.compile_fold J M b join arrows solve

/-- Renaming block targets transports their interpretation. -/
theorem blockArrow_rename {R : List τ} (b : Block Φ L A) (ρ : ∀ {X}, Site L X → Site R X)
    (arrows : LabelArrows J M R T) :
    blockArrow J M arrows (b.rename ρ) = blockArrow J M (fun X p => arrows X (ρ p)) b :=
  Proofs.blockArrow_rename J M b ρ arrows

theorem blockArrow_post {U : C} (b : Block Φ L A) (arrows : LabelArrows J M L T) (k : T ⟶ U) :
    blockArrow J M arrows b ≫ k = blockArrow J M (fun X p => arrows X p ≫ k) b :=
  Proofs.blockArrow_post J M b arrows k

/-- The equations of the compiled blocks supply a solution for the
acyclic compiler's continuation theorem. -/
theorem solves_of_blocks {R : List τ} (code : Extension Φ L R) (arrows : LabelArrows J M R T)
    (hb : ∀ i, arrows _ (code.local i) = blockArrow J M arrows (code.block i)) :
    Solves J M code arrows :=
  Proofs.solves_of_blocks J M code arrows hb

end Distributive

variable [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [FreydCategory.CentralUnit J]

theorem block_denotes (b : Block Φ L A) (Γ : List τ) :
    RegionDenotes J M (b.typing Γ)
      (J.map (snd (ctxObj M Γ) (M.obj A)) ≫
        blockArrow J M (fun _ s => J.map (LinearChain.Categorical.siteArrow M s)) b) :=
  Proofs.block_denotes J M b Γ

/-- The structural denotation of the actual CFG implements the admitted RVSDG
term and returns through the single typed external label. -/
theorem region_denotes (b : Body Φ A B) :
    RegionDenotes J M (regionTyping b)
      (J.map (snd (ctxObj M []) (M.obj A)) ≫ denoteForm J M (.body b) ≫
        J.map (labelInject M (L := [B]) 0 rfl)) :=
  Proofs.region_denotes J M b

/-- Decode the LambdaSSA join label and run any typed continuation. It has
the same denotation as composing that continuation after the γ lowering. -/
theorem denoteRegion_join [RegionTypingCoherent (Φ := Φ) J M]
    (b : Body Φ A B) (join : J.obj (M.obj B) ⟶ T) :
    denoteRegion J M (regionTyping b) ≫ J.map (singletonLabelPayload M B) ≫ join =
      J.map (snd (ctxObj M []) (M.obj A)) ≫ denoteForm J M (.body b) ≫ join :=
  Proofs.denoteRegion_join J M b join

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical
