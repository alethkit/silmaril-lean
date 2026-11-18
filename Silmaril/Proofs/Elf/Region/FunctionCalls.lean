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

theorem root_mem (inventory : Inventory) (entry rounds : Nat) : .localFn entry ∈ reach inventory entry rounds := by
  induction rounds with
  | zero => exact List.Mem.head _
  | succ rounds ih =>
    unfold reach at *
    rw [Function.iterate_succ_apply']
    exact List.mem_append_left _ ih

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

end Silmaril.Elf.Region.Calls.Proofs
