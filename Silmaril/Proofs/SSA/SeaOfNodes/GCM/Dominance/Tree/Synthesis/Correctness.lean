module

public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.Defs
import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.Dominance
open Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree
open Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result} {blocks : List (Target Label)}
variable {a b parent : BlockId Label}

private theorem path_prefix {past : List (BlockId Label)}
    (path : EntryPath cfg b past) (member : a ∈ past) :
    ∃ ps, EntryPath cfg a ps ∧ ps ⊆ past := by
  induction path with
  | entry =>
    obtain rfl := List.mem_singleton.mp member
    exact ⟨_, .entry, fun _ h => h⟩
  | step previous slot edge ih =>
    rcases List.mem_cons.mp member with rfl | prior
    · exact ⟨_, previous.step slot edge, fun _ h => h⟩
    · obtain ⟨ps, hp, sub⟩ := ih prior
      exact ⟨ps, hp, fun _ h => List.mem_cons_of_mem _ (sub h)⟩

private theorem dominates_refl (b : BlockId Label) : Dominates cfg b b := by
  intro _ path
  cases path <;> exact List.mem_cons_self

private theorem dominates_trans (first : Dominates cfg a parent) (second : Dominates cfg parent b) :
    Dominates cfg a b := by
  intro _ path
  obtain ⟨ps, hp, sub⟩ := path_prefix path (second _ path)
  exact sub (first ps hp)

private theorem entry_dominates (b : BlockId Label) : Dominates cfg none b := by
  intro _ path
  induction path with
  | entry => exact List.mem_cons_self
  | step _ _ _ ih => exact List.mem_cons_of_mem _ ih

private theorem dominates_entry (dom : Dominates cfg a none) : a = none :=
  List.mem_singleton.mp (dom _ .entry)

private theorem dominator_reachable (reachable : Reachable cfg b) (dom : Dominates cfg a b) :
    Reachable cfg a := by
  obtain ⟨past, path⟩ := reachable
  obtain ⟨ps, hp, _⟩ := path_prefix path (dom past path)
  exact ⟨ps, hp⟩

private theorem dominates_total_on_path {x : BlockId Label} {past : List (BlockId Label)}
    (path : EntryPath cfg b past) (ha : Dominates cfg a b) (hx : Dominates cfg x b) :
    Dominates cfg a x ∨ Dominates cfg x a := by
  induction path with
  | entry =>
    obtain rfl := dominates_entry ha
    exact .inl (entry_dominates x)
  | @step src _ dst prior slot edge ih =>
    by_cases eqA : a = some dst
    · subst a
      exact .inr hx
    by_cases eqX : x = some dst
    · subst x
      exact .inl ha
    exact ih
      (fun _ p => (List.mem_cons.mp (ha _ (p.step slot edge))).resolve_left eqA)
      (fun _ p => (List.mem_cons.mp (hx _ (p.step slot edge))).resolve_left eqX)

private theorem dominates_antisymm (reachable : Reachable cfg b)
    (ab : Dominates cfg a b) (ba : Dominates cfg b a) : a = b := by
  by_cases equal : a = b
  · exact equal
  exfalso
  obtain ⟨past, path⟩ := reachable
  suffices avoided : ∀ {x ps}, EntryPath cfg x ps → a ∉ ps ∧ b ∉ ps by
    exact (avoided path).1 (ab past path)
  intro x ps p
  induction p with
  | entry =>
    constructor
    · intro hit
      have eqA := List.mem_singleton.mp hit
      subst a
      exact equal (dominates_entry ba).symm
    · intro hit
      have eqB := List.mem_singleton.mp hit
      subst b
      exact equal (dominates_entry ab)
  | step prior slot edge ih =>
    constructor
    · intro hit
      rcases List.mem_cons.mp hit with rfl | earlier
      · exact ih.2 ((List.mem_cons.mp (ba _ (prior.step slot edge))).resolve_left (Ne.symm equal))
      · exact ih.1 earlier
    · intro hit
      rcases List.mem_cons.mp hit with rfl | earlier
      · exact ih.1 ((List.mem_cons.mp (ab _ (prior.step slot edge))).resolve_left equal)
      · exact ih.2 earlier

private theorem greatest_dominator {nodes : List (BlockId Label)} (nonempty : nodes ≠ [])
    (total : ∀ u ∈ nodes, ∀ v ∈ nodes, Dominates cfg u v ∨ Dominates cfg v u) :
    ∃ p ∈ nodes, ∀ u ∈ nodes, Dominates cfg u p := by
  induction nodes with
  | nil => exact (nonempty rfl).elim
  | cons node rest ih =>
    by_cases empty : rest = []
    · subst rest
      refine ⟨node, List.mem_cons_self, fun u hu => ?_⟩
      obtain rfl := List.mem_singleton.mp hu
      exact dominates_refl u
    obtain ⟨p, hp, greatest⟩ := ih empty
      (fun u hu v hv => total u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv))
    rcases total node List.mem_cons_self p (List.mem_cons_of_mem _ hp) with np | pn
    · refine ⟨p, List.mem_cons_of_mem _ hp, fun u hu => ?_⟩
      rcases List.mem_cons.mp hu with rfl | earlier
      · exact np
      · exact greatest u earlier
    · refine ⟨node, List.mem_cons_self, fun u hu => ?_⟩
      rcases List.mem_cons.mp hu with rfl | earlier
      · exact dominates_refl u
      · exact dominates_trans (greatest u earlier) pn

variable [DecidableEq (Target Label)]

private theorem live_iff (closed : checkClosed cfg blocks = true) (b : BlockId Label) :
    b ∈ reachableBlocks cfg blocks ↔ Reachable cfg b := by
  simpa only [reachable?, reachesKeeping?, reachableBlocks, decide_eq_true_eq] using reachable?_iff closed b

private theorem mem_strict_iff (closed : checkClosed cfg blocks = true) (reachable : Reachable cfg b) :
    a ∈ strictDominators cfg blocks b ↔ a ≠ b ∧ Dominates cfg a b := by
  simp only [strictDominators, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
    dominates?_iff, closed, reachable, true_and]
  exact ⟨And.right, fun h => ⟨(live_iff closed a).mpr (dominator_reachable reachable h.2), h⟩⟩

theorem immediateParent?_spec (closed : checkClosed cfg blocks = true)
    (reachable : Reachable cfg b) (named : b ≠ none) :
    ∃ parent, immediateParent? cfg blocks b = some parent ∧ Reachable cfg parent ∧
      parent ≠ b ∧ Dominates cfg parent b ∧
      ∀ a, a ≠ b → Dominates cfg a b → Dominates cfg a parent := by
  let strict := strictDominators cfg blocks b
  have root : none ∈ strict :=
    (mem_strict_iff closed reachable).mpr ⟨Ne.symm named, entry_dominates b⟩
  obtain ⟨past, path⟩ := reachable
  have rb : Reachable cfg b := ⟨past, path⟩
  obtain ⟨greatest, member, greatestProp⟩ :=
    greatest_dominator (nodes := strict) (fun empty => by simp [empty] at root)
      (fun u hu v hv => dominates_total_on_path path
        ((mem_strict_iff closed rb).mp hu).2 ((mem_strict_iff closed rb).mp hv).2)
  have findGreatest : strict.all (fun a => dominates? cfg blocks a greatest) = true := by
    apply List.all_eq_true.mpr
    intro a ha
    exact (dominates?_iff a greatest).mpr
      ⟨closed, dominator_reachable rb ((mem_strict_iff closed rb).mp member).2, greatestProp a ha⟩
  cases found : immediateParent? cfg blocks b with
  | none => exact ((List.find?_eq_none.mp found) greatest member findGreatest).elim
  | some parent =>
    obtain ⟨ne, dom⟩ := (mem_strict_iff closed rb).mp (List.mem_of_find?_eq_some found)
    refine ⟨parent, rfl, dominator_reachable rb dom, ne, dom, fun a ane h => ?_⟩
    have allDom : strict.all (fun a => dominates? cfg blocks a parent) = true :=
      List.find?_some (p := fun p => strict.all (fun a => dominates? cfg blocks a p)) found
    exact ((dominates?_iff a parent).mp (List.all_eq_true.mp allDom a
      ((mem_strict_iff closed rb).mpr ⟨ane, h⟩))).2.2

private theorem strict_smaller (closed : checkClosed cfg blocks = true) (rb : Reachable cfg b)
    (rp : Reachable cfg parent) (ne : parent ≠ b) (dom : Dominates cfg parent b) :
    (strictDominators cfg blocks parent).length < (strictDominators cfg blocks b).length := by
  let keep := fun a => decide (a ≠ parent) && dominates? cfg blocks a parent
  have filtered : (strictDominators cfg blocks b).filter keep =
      strictDominators cfg blocks parent := by
    unfold strictDominators
    rw [List.filter_filter]
    apply List.filter_congr
    intro a _
    change (keep a && (decide (a ≠ b) && dominates? cfg blocks a b)) = keep a
    cases test : keep a
    · simp
    · have ha : a ≠ parent ∧ Dominates cfg a parent := by
        simpa [keep, dominates?_iff, closed, rp] using test
      have unequal : a ≠ b := by
        intro same
        subst a
        exact ne (dominates_antisymm rb dom ha.2)
      have retained : dominates? cfg blocks a b = true :=
        (dominates?_iff a b).mpr ⟨closed, rb, dominates_trans ha.2 dom⟩
      simp [unequal, retained]
  rw [← filtered]
  exact List.length_filter_lt_length_iff_exists.mpr
    ⟨parent, (mem_strict_iff closed rb).mpr ⟨ne, dom⟩, by simp [keep]⟩

private theorem strict_length_le (b : BlockId Label) :
    (strictDominators cfg blocks b).length ≤ (reachableBlocks cfg blocks).length :=
  List.length_filter_le _ _

private theorem strict_length_pos (closed : checkClosed cfg blocks = true)
    (reachable : Reachable cfg b) (named : b ≠ none) :
    0 < (strictDominators cfg blocks b).length :=
  List.length_pos_of_mem ((mem_strict_iff closed reachable).mpr
    ⟨Ne.symm named, entry_dominates b⟩)

private theorem trace_exists (closed : checkClosed cfg blocks = true) (fuel : Nat)
    (rb : Reachable cfg b) (bound : (strictDominators cfg blocks b).length ≤ fuel) :
    ∃ path, traceAddress? cfg blocks fuel b = some path := by
  induction fuel generalizing b with
  | zero =>
    cases b with
    | none => exact ⟨[], rfl⟩
    | some child =>
      have positive := strict_length_pos closed rb (by simp)
      omega
  | succ fuel ih =>
    cases b with
    | none => exact ⟨[], rfl⟩
    | some child =>
      obtain ⟨parent, found, rp, ne, dom, _⟩ := immediateParent?_spec closed rb (by simp)
      have less := strict_smaller closed rb rp ne dom
      obtain ⟨path, traced⟩ := ih rp (by omega)
      refine ⟨path ++ [(reachableBlocks cfg blocks).idxOf (some child)], ?_⟩
      simp [traceAddress?, found, traced]

private theorem trace_more {fuel more : Nat} {path : List Nat}
    (traced : traceAddress? cfg blocks fuel b = some path) (le : fuel ≤ more) :
    traceAddress? cfg blocks more b = some path := by
  induction fuel generalizing b more path with
  | zero =>
    cases b with
    | none => simpa [traceAddress?] using traced
    | some child => simp [traceAddress?] at traced
  | succ fuel ih =>
    cases b with
    | none => simpa [traceAddress?] using traced
    | some child =>
      cases more with
      | zero => omega
      | succ more =>
        cases found : immediateParent? cfg blocks (some child) with
        | none => simp [traceAddress?, found] at traced
        | some parent =>
          cases parentPath : traceAddress? cfg blocks fuel parent with
          | none => simp [traceAddress?, found, parentPath] at traced
          | some ps =>
            have extended := ih parentPath (Nat.le_of_succ_le_succ le)
            simpa [traceAddress?, found, extended, parentPath] using traced

theorem traceAddress?_some (closed : checkClosed cfg blocks = true) (reachable : Reachable cfg b) :
    ∃ path, traceAddress? cfg blocks (reachableBlocks cfg blocks).length b = some path :=
  trace_exists closed _ reachable (strict_length_le b)

private theorem proposed_root : proposedAddress cfg blocks none = [] := by
  simp [proposedAddress, traceAddress?]

private theorem proposed_step (closed : checkClosed cfg blocks = true) {child : Target Label}
    (rb : Reachable cfg (some child)) (rp : Reachable cfg parent)
    (found : immediateParent? cfg blocks (some child) = some parent)
    (ne : parent ≠ some child) (dom : Dominates cfg parent (some child)) :
    proposedAddress cfg blocks (some child) =
      proposedAddress cfg blocks parent ++ [(reachableBlocks cfg blocks).idxOf (some child)] := by
  let fuel := (reachableBlocks cfg blocks).length
  have less := strict_smaller closed rb rp ne dom
  have bound : (strictDominators cfg blocks (some child)).length ≤ fuel :=
    strict_length_le (some child)
  obtain ⟨path, traced⟩ := trace_exists closed (fuel - 1) rp (by omega)
  have tracedMore := trace_more traced (Nat.sub_le fuel 1)
  have childTrace : traceAddress? cfg blocks fuel (some child) =
      some (path ++ [(reachableBlocks cfg blocks).idxOf (some child)]) := by
    rw [show fuel = (fuel - 1) + 1 by omega]
    simp [traceAddress?, found, traced]
  change (traceAddress? cfg blocks fuel (some child)).getD [] =
    (traceAddress? cfg blocks fuel parent).getD [] ++ [_]
  rw [childTrace, tracedMore]
  rfl

private theorem proposed_last (closed : checkClosed cfg blocks = true) {child : Target Label}
    (reachable : Reachable cfg (some child)) :
    (proposedAddress cfg blocks (some child)).getLast? =
      some ((reachableBlocks cfg blocks).idxOf (some child)) := by
  obtain ⟨parent, found, rp, ne, dom, _⟩ := immediateParent?_spec closed reachable (by simp)
  rw [proposed_step closed reachable rp found ne dom, List.getLast?_concat]

private theorem proposed_injective (closed : checkClosed cfg blocks = true)
    (ra : Reachable cfg a) (rb : Reachable cfg b)
    (same : proposedAddress cfg blocks a = proposedAddress cfg blocks b) : a = b := by
  have last := congrArg List.getLast? same
  cases a <;> cases b
  · rfl
  · rw [proposed_root, proposed_last closed rb] at last
    contradiction
  · rw [proposed_last closed ra, proposed_root] at last
    contradiction
  · rw [proposed_last closed ra, proposed_last closed rb] at last
    have recover {x} (reachable : Reachable cfg x) :
        (reachableBlocks cfg blocks)[(reachableBlocks cfg blocks).idxOf x]? = some x := by
      have bound := List.idxOf_lt_length_of_mem ((live_iff closed _).mpr reachable)
      exact List.getElem?_eq_some_iff.mpr ⟨bound, List.getElem_idxOf bound⟩
    have ha := recover ra
    rw [Option.some.inj last, recover rb] at ha
    exact (Option.some.inj ha).symm

private theorem proposed_prefix_root (closed : checkClosed cfg blocks = true)
    (ra : Reachable cfg a) :
    List.IsPrefix (proposedAddress cfg blocks a) (proposedAddress cfg blocks none) ↔
      Dominates cfg a none := by
  constructor
  · intro ancestry
    have same := ancestry.eq_of_length_le (by simp [proposed_root])
    obtain rfl := proposed_injective closed ra ⟨[none], .entry⟩ same
    exact dominates_refl none
  · intro dom
    obtain rfl := dominates_entry dom
    exact ⟨[], by simp⟩

private theorem proposed_prefix_aux (closed : checkClosed cfg blocks = true)
    (ra : Reachable cfg a) (rb : Reachable cfg b) (fuel : Nat)
    (bound : (strictDominators cfg blocks b).length ≤ fuel) :
    List.IsPrefix (proposedAddress cfg blocks a) (proposedAddress cfg blocks b) ↔
      Dominates cfg a b := by
  induction fuel generalizing b with
  | zero =>
    cases b with
    | none => exact proposed_prefix_root closed ra
    | some child =>
      have positive := strict_length_pos closed rb (by simp)
      omega
  | succ fuel ih =>
    cases b with
    | none => exact proposed_prefix_root closed ra
    | some child =>
      obtain ⟨parent, found, rp, ne, dom, allDom⟩ := immediateParent?_spec closed rb (by simp)
      have less := strict_smaller closed rb rp ne dom
      have parentIff := ih rp (by omega)
      have step := proposed_step closed rb rp found ne dom
      have parentPrefix : List.IsPrefix (proposedAddress cfg blocks parent)
          (proposedAddress cfg blocks (some child)) := ⟨_, step.symm⟩
      by_cases same : a = some child
      · subst a
        exact ⟨fun _ => dominates_refl _, fun _ => ⟨[], by simp⟩⟩
      constructor
      · intro ancestry
        have shorter := ancestry.length_le
        have unequal : (proposedAddress cfg blocks a).length ≠
            (proposedAddress cfg blocks (some child)).length :=
          fun lengths => same (proposed_injective closed ra rb (ancestry.eq_of_length lengths))
        have stepLength : (proposedAddress cfg blocks (some child)).length =
            (proposedAddress cfg blocks parent).length + 1 := by
          simpa [List.length_append] using congrArg List.length step
        have toParent := List.prefix_of_prefix_length_le ancestry parentPrefix (by omega)
        exact dominates_trans (parentIff.mp toParent) dom
      · intro ancestor
        exact (parentIff.mpr (allDom a same ancestor)).trans parentPrefix

theorem proposedAddress_prefix_iff (closed : checkClosed cfg blocks = true)
    (ra : Reachable cfg a) (rb : Reachable cfg b) :
    List.IsPrefix (proposedAddress cfg blocks a) (proposedAddress cfg blocks b) ↔
      Dominates cfg a b :=
  proposed_prefix_aux closed ra rb _ (strict_length_le b)

theorem check_proposedAddress (closed : checkClosed cfg blocks = true) :
    Tree.check cfg blocks (proposedAddress cfg blocks) = true := by
  simp only [Tree.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨closed, proposed_root⟩, ?_⟩, ?_⟩
  · intro b member
    cases b with
    | none => rfl
    | some child =>
      have rb := (live_iff closed _).mp member
      obtain ⟨parent, found, rp, ne, dom, _⟩ := immediateParent?_spec closed rb (by simp)
      have step := proposed_step closed rb rp found ne dom
      rw [proposed_last closed rb]
      simp only [Option.isNone_some, Bool.false_or, Option.any_some, List.any_eq_true]
      exact ⟨parent, (live_iff closed parent).mpr rp, decide_eq_true step⟩
  · intro a memberA b memberB
    have ra := (live_iff closed a).mp memberA
    have rb := (live_iff closed b).mp memberB
    refine ⟨proposed_injective closed ra rb, ?_⟩
    rw [Bool.eq_iff_iff, List.isPrefixOf_iff_prefix, proposedAddress_prefix_iff closed ra rb,
      dominates?_iff]
    simp [closed, rb]

theorem synthesize?_isSome_iff (number : BlockId Label → Nat) (injective : Function.Injective number) :
    (synthesize? cfg blocks number injective).isSome = true ↔ checkClosed cfg blocks = true := by
  by_cases closed : checkClosed cfg blocks = true
  · simp [synthesize?, certify?, check_proposedAddress closed, closed]
  · have rejected : Tree.check cfg blocks (proposedAddress cfg blocks) = false := by
      simp [Tree.check, closed]
    simp [synthesize?, certify?, rejected, closed]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis
