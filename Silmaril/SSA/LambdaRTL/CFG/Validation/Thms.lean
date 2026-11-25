module

public import Silmaril.SSA.LambdaRTL.CFG.Validation.Defs
public import Silmaril.SSA.LambdaRTL.Institution.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Validation

@[expose] public section
namespace Silmaril.SSA.LambdaRTL.CFG.Validation

universe v w
variable {V K L : Type w} {F : Type v}

/-- Literal equality is contained in coherent, view-preserving renaming. -/
theorem exact_subset_iso (view : K → L) :
    exactCFG (V := V) (F := F) ⊆ cfgIso view :=
  Proofs.SSA.LambdaRTL.CFG.Validation.exact_subset_iso view

theorem subset_close (base : CFGRelation V K F) : base ⊆ close base :=
  fun _ h => Relation.ReflTransGen.single (.inl h)

theorem close_mono {R S : CFGRelation V K F} (h : R ⊆ S) : close R ⊆ close S := by
  rintro ⟨source, target⟩ path
  exact Relation.ReflTransGen.mono (fun _ _ edge => edge.imp (fun edge => h edge) id) source target path

theorem regionImage_mono {R S : CFGRelation V K F} (h : R ⊆ S) :
    regionImage R ⊆ regionImage S := by
  rintro _ ⟨source, target, edge, left, right⟩
  exact ⟨source, target, h edge, left, right⟩

theorem cfgIso_blocks (view : K → L) {source target : CFG V K F}
    (h : (source, target) ∈ cfgIso view) {block : K × Block V K F} (hb : block ∈ source.blocks) :
    ∃ candidate ∈ target.blocks, (block.2, candidate.2) ∈ blockIso view :=
  Proofs.SSA.LambdaRTL.CFG.Validation.cfgIso_blocks view h hb

theorem contractEntry_sound [DecidableEq V] [DecidableEq K] {source target : CFG V K F}
    (h : contractEntry? source = some target) : EntryRelay source target :=
  Proofs.SSA.LambdaRTL.CFG.Validation.contractEntry_sound h

section Semantics

variable {M : Type w → Type w} {α : Type w} [Monad M] [LawfulMonad M] [DecidableEq V]
  [DecidableEq K]

/-- The guard preserves the actual CFG result, including the full final store. -/
theorem entryRelay_run (m : Model F M α) (σ : V → α) {source target : CFG V K F}
    (relay : EntryRelay source target) : source.run m σ = target.run m σ :=
  Proofs.SSA.LambdaRTL.CFG.Validation.entryRelay_run m σ relay

/-- Every certified finite chain agrees on the viewed exit, value and store. -/
theorem close_run (view : K → L) (m : Model F M α) (σ : V → α)
    {source target : CFG V K F} (h : (source, target) ∈ close (cfgIso view)) :
    observe view <$> source.run m σ = observe view <$> target.run m σ :=
  Proofs.SSA.LambdaRTL.CFG.Validation.close_run view m σ h

/-- The existing embedding carries the same result to dominator-tree regions. -/
theorem region_run (view : K → L) (m : Model F M α) (σ : V → α)
    {source target : Region V K F} (h : (source, target) ∈ regionImage (close (cfgIso view))) :
    observe view <$> source.evalRTL m σ = observe view <$> target.evalRTL m σ :=
  Proofs.SSA.LambdaRTL.CFG.Validation.region_run view m σ h

end Semantics

/-- The region judgment is satisfied in the existing full-store institution
with the specified view on exit labels. This compares all input stores. -/
theorem region_satisfies {V K L F α : Type} {M : Type → Type}
    [Monad M] [LawfulMonad M] [DecidableEq V] [DecidableEq K]
    (view : K → L) (model : Model F M α) (ctx : Finset V)
    {source target : Region V K F} (h : (source, target) ∈ regionImage (close (cfgIso view))) :
    (Institution.rtlFullRoom V K M α (fun a b => observe view <$> a = observe view <$> b) ⟨F⟩).Sat
      (CategoryTheory.Discrete.mk model) ⟨ctx, source, target⟩ :=
  fun σ => region_run view model σ h

end Silmaril.SSA.LambdaRTL.CFG.Validation
