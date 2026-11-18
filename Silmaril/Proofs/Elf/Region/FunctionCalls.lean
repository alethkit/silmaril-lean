module

public import Silmaril.Elf.Region.Calls.Defs
public import Silmaril.Semantics.Function.Thms

public section
namespace Silmaril.Elf.Region.Calls.Proofs
open Silmaril.Semantics.Function
open Silmaril.Machine.Region (BinaryObject)

theorem readable_rows (source : BinaryObject) (plan : Plan) :
    ReadableRows source plan (rows (extract source plan)) := by
  rintro name body ⟨row, inInventory, available, rfl, entry⟩
  obtain ⟨spec, inPlan, rfl⟩ := List.mem_map.mp inInventory
  cases read : readWindow source spec.entry spec.size with
  | none => simp [extractRow, read] at available
  | some bytes =>
    simp only [extractRow, read] at entry ⊢
    exact ⟨inPlan, entry, bytes, rfl⟩

theorem finding_evidence {source : BinaryObject} {plan : Plan} {row : Row} {finding : Finding}
    (member : row ∈ extract source plan) (available : row.available = true) (found : finding ∈ row.findings) :
    FindingAt source plan finding := by
  obtain ⟨body, inPlan, rfl⟩ := List.mem_map.mp member
  cases read : readWindow source body.entry body.size with
  | none => simp [extractRow, read] at available
  | some bytes =>
    simp only [extractRow, read] at found
    exact ⟨body, inPlan, bytes, read, List.mem_flatMap.mp found⟩

theorem mem_directArcs {inventory : Inventory} {source : Nat} {dest : Node signature} :
    (source, dest) ∈ directArcs inventory ↔ DirectEdge inventory (.localFn source) dest := by
  constructor
  · intro mem
    obtain ⟨row, inInventory, localMem⟩ := List.mem_flatMap.mp mem
    obtain ⟨finding, inRow, hit⟩ := List.mem_filterMap.mp localMem
    cases finding with
    | direct site target callee =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hit
      obtain ⟨rfl, rfl⟩ := hit
      exact ⟨⟨site, .direct, callee⟩, ⟨row, inInventory, target, inRow⟩, rfl, rfl, rfl⟩
    | indirect | gap => cases hit
  · rintro ⟨⟨site, tag, callee⟩, evidence, rfl, sourceEq, destEq⟩
    cases sourceEq
    cases destEq
    obtain ⟨row, inInventory, target, inRow⟩ := evidence
    exact List.mem_flatMap.mpr ⟨row, inInventory, List.mem_filterMap.mpr ⟨_, inRow, rfl⟩⟩

theorem successor_iff {inventory : Inventory} {source dest : Node signature} :
    dest ∈ successors inventory source ↔ DirectEdge inventory source dest := by
  cases source with
  | foreign name => simp [successors, DirectEdge, directGraph, foreign_leaf]
  | localFn source =>
    constructor
    · intro mem
      obtain ⟨⟨caller, callee⟩, inArcs, hit⟩ := List.mem_filterMap.mp mem
      by_cases eq : caller = source
      · simp [eq] at hit
        subst caller; subst callee
        exact mem_directArcs.mp inArcs
      · simp [eq] at hit
    · intro edge
      exact List.mem_filterMap.mpr ⟨(source, dest), mem_directArcs.mpr edge, by simp⟩

theorem iterate_sound {inventory : Inventory} {seed : List (Node signature)} {rounds : Nat}
    {witness : Node signature → Prop} (seed_sound : ∀ node ∈ seed, witness node)
    (forward : ∀ source dest, witness source → DirectEdge inventory source dest → witness dest)
    {dest : Node signature} (mem : dest ∈ (expand inventory)^[rounds] seed) : witness dest := by
  induction rounds generalizing dest with
  | zero => exact seed_sound dest mem
  | succ rounds ih =>
    rw [Function.iterate_succ_apply'] at mem
    rcases List.mem_append.mp mem with known | added
    · exact ih known
    · obtain ⟨source, inSeen, edge⟩ := List.mem_flatMap.mp (List.mem_filter.mp added).1
      exact forward source dest (ih inSeen) (successor_iff.mp edge)

theorem seed_mem (inventory : Inventory) (rounds : Nat) {seed : List (Node signature)} {node : Node signature}
    (mem : node ∈ seed) : node ∈ (expand inventory)^[rounds] seed := by
  induction rounds with
  | zero => exact mem
  | succ rounds ih =>
    rw [Function.iterate_succ_apply']
    exact List.mem_append_left _ ih

theorem root_mem (inventory : Inventory) (entry rounds : Nat) : .localFn entry ∈ reach inventory entry rounds :=
  seed_mem inventory rounds (List.Mem.head _)

theorem nodeEq_true (lhs rhs : Node signature) : nodeEq lhs rhs = true ↔ lhs = rhs := by
  cases lhs <;> cases rhs <;> simp [nodeEq]

theorem step_closed {inventory : Inventory} {seen : List (Node signature)} (fixed : expand inventory seen = seen)
    {source dest : Node signature} (source_mem : source ∈ seen) (edge : DirectEdge inventory source dest) :
    dest ∈ seen := by
  by_contra absent
  have noMatch : seen.any (nodeEq dest) = false := by
    rw [Bool.eq_false_iff]
    intro found
    obtain ⟨other, mem, eq⟩ := List.any_eq_true.mp found
    exact absent ((nodeEq_true dest other).mp eq |>.symm ▸ mem)
  have new : dest ∈ expand inventory seen := List.mem_append_right _ (List.mem_filter.mpr
    ⟨List.mem_flatMap.mpr ⟨source, source_mem, successor_iff.mpr edge⟩, by simp [noMatch]⟩)
  exact absent (fixed ▸ new)

theorem fixed_of_stable {inventory : Inventory} {seen : List (Node signature)}
    (done : stable inventory seen = true) : expand inventory seen = seen := by
  have equal : (expand inventory seen).length = seen.length := beq_iff_eq.mp done
  unfold expand at equal ⊢
  simp only [List.length_append] at equal
  rw [List.length_eq_zero_iff.mp (Nat.add_left_cancel (equal.trans (Nat.add_zero seen.length).symm)),
    List.append_nil]

theorem path_iff_reach {inventory : Inventory} {entry : Nat} {leaf : Stub} :
    CallPath (directGraph (analysis inventory).may) (.localFn entry) (.foreign leaf) ↔
      Reachable (directGraph (analysis inventory).may) (.localFn entry) (.foreign leaf) := by
  refine ⟨Relation.TransGen.to_reflTransGen, fun path => ?_⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with impossible | nonempty
  · cases impossible
  · exact nonempty

theorem nonempty_complete {inventory : Inventory} {entry rounds : Nat}
    (fixed : expand inventory (nonemptyReach inventory entry rounds) = nonemptyReach inventory entry rounds)
    {dest : Node signature} (path : CallPath (directGraph (analysis inventory).may) (.localFn entry) dest) :
    dest ∈ nonemptyReach inventory entry rounds := by
  induction path with
  | single edge => exact seed_mem inventory rounds (successor_iff.mpr edge)
  | tail _ edge ih => exact step_closed fixed ih edge

theorem mem_frontier {leaf : Stub} {seen : List (Node signature)} :
    leaf ∈ seen.filterMap (fun node => match node with | .foreign stub => some stub | _ => none) ↔
      .foreign leaf ∈ seen := by
  rw [List.mem_filterMap]
  refine ⟨?_, fun mem => ⟨.foreign leaf, mem, rfl⟩⟩
  rintro ⟨node, mem, result⟩
  cases node with
  | localFn _ => cases result
  | foreign _ => cases result; exact mem

theorem mem_knownCalls {inventory : Inventory} {seen : List (Node signature)} {caller : Nat}
    {dest : Node signature} :
    (caller, dest) ∈ (directArcs inventory).filter (fun (source, _) => seen.any (nodeEq (.localFn source))) ↔
      DirectEdge inventory (.localFn caller) dest ∧ .localFn caller ∈ seen := by
  rw [List.mem_filter, mem_directArcs, List.any_eq_true]
  simp [nodeEq_true]

theorem bounded_cover {inventory : Inventory} {targets : CallSite signature → Option (Set (Node signature))}
    {actual : Calls signature} (top : CallGraphProblem actual (analysis inventory))
    (narrow : ∀ edge, actual edge → edge.dispatch = .indirect → admits (targets edge.origin) edge.callee) :
    CallGraphProblem actual (boundedAnalysis inventory targets) := by
  intro edge real
  have covered := top real
  rcases edge with ⟨origin, tag, dest⟩
  cases tag with
  | direct => exact covered
  | indirect =>
    obtain ⟨_, ⟨_, recorded⟩, _⟩ := covered
    exact ⟨targets origin, ⟨rfl, recorded⟩, narrow _ real rfl⟩

theorem bounded_embed (inventory : Inventory) (targets : CallSite signature → Option (Set (Node signature))) :
    MayCover (boundedAnalysis inventory targets).may (analysis inventory).may := by
  intro edge mem
  rcases edge with ⟨origin, tag, dest⟩
  cases tag with
  | direct => exact mem
  | indirect =>
    obtain ⟨_, ⟨_, recorded⟩, _⟩ := mem
    exact ⟨none, ⟨rfl, recorded⟩, trivial⟩

end Silmaril.Elf.Region.Calls.Proofs
