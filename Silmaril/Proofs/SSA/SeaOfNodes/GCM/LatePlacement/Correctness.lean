module

public import Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Defs
import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LatePlacement

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.Dominance
open Silmaril.SSA.SeaOfNodes.GCM.LatePlacement

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result} {tree : DominatorTree cfg}
variable {blocks : List (Target Label)} {uses : List (Use Label)}
variable {sites : List (Use Label × Point Label)} {late : BlockId Label}

private theorem valid_of_check {p : Point Label} (checked : p.valid? tree = true) :
    p.Valid cfg := by
  simp only [Point.valid?, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨tree.reachable_sound checked.1, checked.2⟩

private theorem check_of_valid (complete : tree.Complete) {p : Point Label} (h : p.Valid cfg) :
    p.valid? tree = true := by
  simp only [Point.valid?, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨complete.reachable_complete h.1, h.2⟩

theorem resolveUses?_spec (resolved : resolveUses? tree uses = some sites) :
    sites.map Prod.fst = uses ∧
      ∀ site ∈ sites, site.1.point? cfg = some site.2 ∧ site.2.Valid cfg := by
  induction uses generalizing sites with
  | nil =>
    simp only [resolveUses?, Option.some.injEq] at resolved
    subst sites
    simp
  | cons use rest ih =>
    cases readEq : use.point? cfg with
    | none => simp [resolveUses?, readEq] at resolved
    | some read =>
      by_cases valid : read.valid? tree = true
      · cases tailEq : resolveUses? tree rest with
        | none => simp [resolveUses?, readEq, tailEq] at resolved
        | some more =>
          have eq : (use, read) :: more = sites := by
            simpa [resolveUses?, readEq, valid, tailEq] using resolved
          subst sites
          obtain ⟨original, tailFacts⟩ := ih tailEq
          refine ⟨by simp [original], ?_⟩
          intro site member
          rcases List.mem_cons.mp member with rfl | earlier
          · exact ⟨readEq, valid_of_check valid⟩
          · exact tailFacts site earlier
      · simp [resolveUses?, readEq, valid] at resolved

private theorem resolveUses?_exists (complete : tree.Complete)
    (valid : ∀ use ∈ uses, ∃ read, use.point? cfg = some read ∧ read.Valid cfg) :
    ∃ sites, resolveUses? tree uses = some sites := by
  induction uses with
  | nil => exact ⟨[], rfl⟩
  | cons use rest ih =>
    obtain ⟨read, point, checked⟩ := valid use List.mem_cons_self
    obtain ⟨sites, resolved⟩ := ih (fun u hu => valid u (List.mem_cons_of_mem _ hu))
    refine ⟨(use, read) :: sites, ?_⟩
    simp [resolveUses?, point, check_of_valid complete checked, resolved]

private theorem found_sites (found : lateBound? tree blocks uses = some late) :
    ∃ sites, resolveUses? tree uses = some sites ∧ sites ≠ [] ∧
      (commonDominators tree blocks sites).maxOn? (fun block => (tree.address block).length) =
        some late := by
  cases resolved : resolveUses? tree uses with
  | none => simp [lateBound?, resolved] at found
  | some sites =>
    cases sites with
    | nil => simp [lateBound?, resolved] at found
    | cons site rest => exact ⟨site :: rest, rfl, by simp, by simpa [lateBound?, resolved] using found⟩

private theorem sites_of_use (same : sites.map Prod.fst = uses) {use : Use Label}
    (member : use ∈ uses) : ∃ read, (use, read) ∈ sites := by
  rw [← same] at member
  obtain ⟨⟨_, read⟩, site, rfl⟩ := List.mem_map.mp member
  exact ⟨read, site⟩

private theorem use_of_site (same : sites.map Prod.fst = uses) {site : Use Label × Point Label}
    (member : site ∈ sites) : site.1 ∈ uses := by
  rw [← same]
  exact List.mem_map_of_mem member

private theorem path_member_reachable {a b : BlockId Label} {past : List (BlockId Label)}
    (path : EntryPath cfg b past) (member : a ∈ past) : Reachable cfg a := by
  induction path with
  | entry =>
    obtain rfl := List.mem_singleton.mp member
    exact ⟨[none], .entry⟩
  | step p slot actual ih =>
    rcases List.mem_cons.mp member with rfl | prior
    · exact ⟨_, p.step slot actual⟩
    · exact ih prior

private theorem mem_common_iff (complete : tree.Complete)
    (valid : ∀ site ∈ sites, site.2.Valid cfg) {block : BlockId Label} :
    block ∈ commonDominators tree blocks sites ↔
      block ∈ NaturalLoop.vertices blocks ∧ Reachable cfg block ∧
        ∀ site ∈ sites, Dominates cfg block site.2.block := by
  simp only [commonDominators, List.mem_filter, Bool.and_eq_true, List.all_eq_true,
    List.isPrefixOf_iff_prefix]
  constructor
  · rintro ⟨member, reachable, ancestry⟩
    exact ⟨member, tree.reachable_sound reachable,
      fun site hs => tree.prefix_sound (valid site hs).1 (ancestry site hs)⟩
  · rintro ⟨member, reachable, dominates⟩
    exact ⟨member, complete.reachable_complete reachable,
      fun site hs => complete.prefix_complete (valid site hs).1 (dominates site hs)⟩

private theorem entry_common (tree : DominatorTree cfg) (complete : tree.Complete)
    (blocks : List (Target Label)) (sites : List (Use Label × Point Label)) :
    none ∈ commonDominators tree blocks sites := by
  have entry : Reachable cfg none := ⟨[none], .entry⟩
  simp [commonDominators, NaturalLoop.vertices, complete.reachable_complete entry,
    tree.entry_address]

theorem lateBound?_isSome_iff (complete : tree.Complete) :
    (lateBound? tree blocks uses).isSome = true ↔
      uses ≠ [] ∧ ∀ use ∈ uses, ∃ read, use.point? cfg = some read ∧ read.Valid cfg := by
  constructor
  · intro existsBound
    have ⟨late, found⟩ := Option.isSome_iff_exists.mp existsBound
    obtain ⟨sites, resolved, nonempty, _⟩ := found_sites found
    obtain ⟨same, facts⟩ := resolveUses?_spec resolved
    refine ⟨fun empty => nonempty (List.map_eq_nil_iff.mp (same.trans empty)), ?_⟩
    intro use member
    obtain ⟨read, present⟩ := sites_of_use same member
    exact ⟨read, facts (use, read) present⟩
  · rintro ⟨nonempty, valid⟩
    obtain ⟨sites, resolved⟩ := resolveUses?_exists complete valid
    have same := (resolveUses?_spec resolved).1
    have hasSites : sites ≠ [] := fun empty => nonempty (same.symm.trans (by simp [empty]))
    simpa [lateBound?, resolved, hasSites] using
      (List.isSome_maxOn?_of_mem (f := fun block => (tree.address block).length)
        (entry_common tree complete blocks sites))

variable [DecidableEq (Target Label)]

theorem lateBound?_spec (complete : tree.Complete) (closed : checkClosed cfg blocks = true)
    (found : lateBound? tree blocks uses = some late) :
    Reachable cfg late ∧ ∀ block,
      Dominates cfg block late ↔
        ∀ use ∈ uses, ∃ read, use.point? cfg = some read ∧ Dominates cfg block read.block := by
  obtain ⟨sites, resolved, nonempty, largest⟩ := found_sites found
  obtain ⟨same, facts⟩ := resolveUses?_spec resolved
  have valid (site) (member : site ∈ sites) := (facts site member).2
  obtain ⟨_, reachable, common⟩ :=
    (mem_common_iff complete valid).mp (List.maxOn?_mem largest)
  refine ⟨reachable, fun block => ?_⟩
  constructor
  · intro dominates use member
    obtain ⟨read, present⟩ := sites_of_use same member
    have ⟨point, readValid⟩ := facts (use, read) present
    refine ⟨read, point, tree.prefix_sound readValid.1 ?_⟩
    exact (complete.prefix_complete reachable dominates).trans
      (complete.prefix_complete readValid.1 (common (use, read) present))
  · intro dominatesAll
    have dominates (site) (member : site ∈ sites) : Dominates cfg block site.2.block := by
      obtain ⟨read, point, dominance⟩ := dominatesAll site.1 (use_of_site same member)
      have readEq := Option.some.inj ((facts site member).1.symm.trans point)
      simpa [readEq] using dominance
    obtain ⟨site, present⟩ := List.exists_mem_of_ne_nil sites nonempty
    have readReachable := (valid site present).1
    obtain ⟨past, path⟩ := (valid site present).1
    obtain ⟨prefixPath, blockPath⟩ := path_member_reachable path (dominates site present past path)
    have blockMember : block ∈ commonDominators tree blocks sites :=
      (mem_common_iff complete valid).mpr
        ⟨path_endpoint_mem closed blockPath, ⟨prefixPath, blockPath⟩, dominates⟩
    have depth : (tree.address block).length ≤ (tree.address late).length := by
      have maximum := List.le_apply_get_maxOn?_of_mem
        (f := fun block => (tree.address block).length) blockMember
      simpa [largest] using maximum
    exact tree.prefix_sound reachable (List.prefix_of_prefix_length_le
      (complete.prefix_complete readReachable (dominates site present))
      (complete.prefix_complete readReachable (common site present)) depth)

theorem legal_iff_lateBound (complete : tree.Complete) (closed : checkClosed cfg blocks = true)
    (found : lateBound? tree blocks uses = some late)
    (operands : List (Point Label)) (candidate : Point Label) :
    Legal cfg operands uses candidate ↔
      candidate.Valid cfg ∧
      (∀ operand ∈ operands, operand.Valid cfg ∧ operand.AvailableAt cfg candidate) ∧
      Dominates cfg candidate.block late ∧
      ∀ use ∈ uses, ∀ read, use.point? cfg = some read →
        candidate.block = read.block → candidate.cut ≤ read.cut := by
  have bound := (lateBound?_spec complete closed found).2 candidate.block
  constructor
  · intro legal
    refine ⟨legal.candidate_valid, legal.operands_available, bound.mpr ?_, ?_⟩
    · intro use member
      obtain ⟨read, point, _, available⟩ := legal.uses_available use member
      exact ⟨read, point, available.dominates⟩
    · intro use member read point same
      obtain ⟨resolved, resolvedEq, _, available⟩ := legal.uses_available use member
      obtain rfl := Option.some.inj (point.symm.trans resolvedEq)
      exact available.local_order same
  · rintro ⟨valid, available, dominates, localOrder⟩
    obtain ⟨sites, resolved, _, _⟩ := found_sites found
    obtain ⟨same, facts⟩ := resolveUses?_spec resolved
    refine ⟨valid, available, ?_⟩
    intro use member
    obtain ⟨read, inSites⟩ := sites_of_use same member
    obtain ⟨point, readValid⟩ := facts (use, read) inSites
    obtain ⟨target, targetPoint, blockDom⟩ := bound.mp dominates use member
    obtain rfl := Option.some.inj (point.symm.trans targetPoint)
    exact ⟨read, point, readValid, ⟨blockDom, localOrder use member read point⟩⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LatePlacement
