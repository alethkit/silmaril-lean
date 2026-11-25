module

public import Silmaril.SSA.LambdaRTL.CFG.Validation.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Thms

@[expose] public section
namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Validation

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Validation

universe v w
variable {V K L : Type w} {F : Type v}

private theorem term_relabel_id (term : Term V K F) : term.relabel id = term := by
  induction term <;> simp_all [Term.relabel]

private theorem body_relabel_id (body : Body V K F) : body.relabel id = body := by
  induction body <;> simp_all [Body.relabel, term_relabel_id]

private theorem blocks_relabel_id (blocks : List (K × Block V K F)) :
    (blocks.map fun entry => (entry.1, entry.2.relabel id)) = blocks := by
  induction blocks with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨label, block⟩
    have hb : block.relabel id = block := by
      cases block
      simp [Block.relabel, body_relabel_id]
    change (label, block.relabel id) :: _ = (label, block) :: tail
    rw [hb, ih]

theorem exact_subset_iso (view : K → L) :
    exactCFG (V := V) (F := F) ⊆ cfgIso view := by
  rintro ⟨source, target⟩ (rfl : source = target)
  refine ⟨Equiv.refl K, fun _ => rfl, ?_⟩
  cases source with
  | mk entry blocks =>
    change CFG.mk entry blocks =
      CFG.mk (entry.relabel id) (blocks.map fun entry => (entry.1, entry.2.relabel id))
    rw [body_relabel_id, blocks_relabel_id]

theorem cfgIso_blocks (view : K → L) {source target : CFG V K F}
    (h : (source, target) ∈ cfgIso view) {block : K × Block V K F} (hb : block ∈ source.blocks) :
    ∃ candidate ∈ target.blocks, (block.2, candidate.2) ∈ blockIso view := by
  rcases h with ⟨rename, hview, heq⟩
  change target = source.relabel rename at heq
  subst target
  exact ⟨(rename block.1, block.2.relabel rename), List.mem_map_of_mem hb, rename, hview, rfl⟩

theorem contractEntry_sound [DecidableEq V] [DecidableEq K] {source target : CFG V K F}
    (h : contractEntry? source = some target) : EntryRelay source target := by
  rcases source with ⟨entry, blocks⟩
  cases blocks with
  | nil => cases entry <;> simp [contractEntry?] at h
  | cons head rest =>
    rcases head with ⟨first, param, body⟩
    cases entry with
    | let1 | let2 => simp [contractEntry?] at h
    | term term =>
      cases term with
      | case => simp [contractEntry?] at h
      | br label value =>
        cases value with
        | unit | pair => simp [contractEntry?] at h
        | var source =>
          change (if label = first ∧ source = param then some ⟨body, rest⟩ else none) =
            some target at h
          split at h
          next equal =>
            obtain ⟨rfl, rfl⟩ := equal
            have ht := Option.some.inj h
            subst target
            exact .contract label source body rest
          next => contradiction

section Semantics

variable {M : Type w → Type w} {α : Type w} [Monad M] [LawfulMonad M] [DecidableEq V]
  [DecidableEq K]

omit [LawfulMonad M] in
private theorem joinAll_eval_congr (m : Model F M α) (σ : V → α)
    {left right : Region V K F} (h : left.evalRTL m σ = right.evalRTL m σ)
    (rest : List (K × Block V K F)) :
    (joinAll left rest).evalRTL m σ = (joinAll right rest).evalRTL m σ := by
  induction rest generalizing left right with
  | nil => exact h
  | cons next rest ih =>
    apply ih
    simp only [Region.evalRTL, h]

theorem entryRelay_run (m : Model F M α) (σ : V → α) {source target : CFG V K F}
    (relay : EntryRelay source target) : source.run m σ = target.run m σ := by
  rw [run_eq_toRegion, run_eq_toRegion]
  cases relay with
  | contract label param body rest =>
    apply joinAll_eval_congr m σ _ rest
    have hupdate : upd σ param (σ param) = σ := by
      funext x
      by_cases hx : x = param <;> simp [upd, hx]
    simp [Body.toRegion, Term.toRegion, Region.evalRTL, Val.eval, hupdate]

theorem cfgIso_run (view : K → L) (m : Model F M α) (σ : V → α)
    {source target : CFG V K F} (h : (source, target) ∈ cfgIso view) :
    observe view <$> source.run m σ = observe view <$> target.run m σ := by
  rcases h with ⟨rename, hview, heq⟩
  change target = source.relabel rename at heq
  subst target
  rw [run_relabel m rename source (fun _ _ _ _ h => rename.injective h), Functor.map_map]
  have hcompose : (fun e : K × α × (V → α) => observe view (rename e.1, e.2)) = observe view := by
    funext result
    change (view (rename result.1), result.2) = (view result.1, result.2)
    rw [hview result.1]
  rw [hcompose]

theorem close_run (view : K → L) (m : Model F M α) (σ : V → α)
    {source target : CFG V K F} (h : (source, target) ∈ close (cfgIso view)) :
    observe view <$> source.run m σ = observe view <$> target.run m σ := by
  change Relation.ReflTransGen _ source target at h
  induction h with
  | refl => rfl
  | tail _ step ih =>
    apply ih.trans
    rcases step with iso | relay
    · exact cfgIso_run view m σ iso
    · rw [entryRelay_run m σ relay]

theorem region_run (view : K → L) (m : Model F M α) (σ : V → α)
    {source target : Region V K F} (h : (source, target) ∈ regionImage (close (cfgIso view))) :
    observe view <$> source.evalRTL m σ = observe view <$> target.evalRTL m σ := by
  rcases h with ⟨graph, candidate, related, rfl, rfl⟩
  simp only [← run_eq_toRegion]
  exact close_run view m σ related

end Semantics

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Validation
