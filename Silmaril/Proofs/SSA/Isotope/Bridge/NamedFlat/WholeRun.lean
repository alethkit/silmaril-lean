module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.WholeRun.Defs
public import Silmaril.Semantics.Elgot.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Semantics

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat Silmaril.SSA.LambdaRTL
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Region (Eval Follow)
open Silmaril.Elgot.Part (Runs)

universe u

variable {V K F α : Type u} {n : Nat}

theorem mem_number {labels : Nat} {index : K → Option (Fin labels)}
    {jump : K × Value α} {i : Nat} {v : Value α} :
    (i, v) ∈ number index jump ↔
      ∃ slot, index jump.1 = some slot ∧ (slot.val, jump.2) = (i, v) := by
  cases h : index jump.1 <;> simp [number, h, Part.mem_some_iff, eq_comm]

variable [DecidableEq V] [DecidableEq K]
variable {graph : CFG V K F} {exits : List K}

local notation "index" => labelIndex graph.blocks exits
local notation "findBlock" => (fun label => graph.blocks.findFinIdx? (fun item => label == Prod.fst item))

omit [DecidableEq V] in
theorem label_cases {label : K} {slot : Fin (graph.blocks.length + exits.length)}
    (numbered : index label = some slot) :
    (∃ i, findBlock label = some i ∧ slot = i.castAdd exits.length) ∨
      (∃ e, findBlock label = none ∧
        exits.findFinIdx? (fun exit => label == exit) = some e ∧
        slot = Fin.natAdd graph.blocks.length e) := by
  cases hit : findBlock label with
  | some i =>
    have eq : i.castAdd exits.length = slot := by simpa [labelIndex, hit] using numbered
    exact .inl ⟨i, rfl, eq.symm⟩
  | none =>
    simp only [labelIndex, hit, Option.map_eq_some_iff] at numbered
    obtain ⟨e, ext, rfl⟩ := numbered
    exact .inr ⟨e, rfl, ext, rfl⟩

variable {prim : F → Value α → Part (Value α)} {store : V → Value α}

local notation "namedStep" => CFG.Cyclic.stepSSA (model prim) graph.blocks store

private theorem step_done {start final : K × Value α} :
    Sum.inl final ∈ namedStep start ↔ findBlock start.1 = none ∧ final = start := by
  cases hit : findBlock start.1 with
  | none => simp [CFG.Cyclic.stepSSA, lookup_index, hit, Part.mem_some_iff]
  | some i =>
    simp [CFG.Cyclic.stepSSA, lookup_index, hit, Part.map_eq_map, Part.mem_map_iff]

omit [DecidableEq K] in
theorem mem_continue {labels : Nat} (idx : K → Option (Fin labels))
    {body : Part ((K × Value α) ⊕ (K × Value α))} {i : Nat} {v : Value α} :
    (i, v) ∈ (body >>= Sum.elim (fun _ => Part.none) (number idx)) ↔
      ∃ jump, Sum.inr jump ∈ body ∧ (i, v) ∈ number idx jump := by
  rw [Part.bind_eq_bind, Part.mem_bind_iff]
  constructor
  · rintro ⟨next, stepped, numbered⟩
    cases next with
    | inl _ => exact (Part.notMem_none _ numbered).elim
    | inr jump => exact ⟨jump, stepped, numbered⟩
  · rintro ⟨jump, stepped, numbered⟩
    exact ⟨.inr jump, stepped, numbered⟩

variable {captures : Fin n → V}
  {target : LambdaSSA.FiniteCFG F graph.blocks.length exits.length n} {env : Env α}

local notation "blockCode" => (fun i => LambdaSSA.Flat.erase (target.block i))

private theorem follow_of_runs (accepted : elaborate graph exits captures = some target)
    {start final : K × Value α} (run : Runs namedStep start final)
    {slot : Fin (graph.blocks.length + exits.length)} (numbered : index start.1 = some slot) :
    ∃ out, (out, final.2) ∈ numberExit exits final ∧
      Follow (instr prim) env blockCode slot.val start.2 () out final.2 () := by
  induction run generalizing slot with
  | done stopped =>
    obtain ⟨miss, rfl⟩ := step_done.mp stopped
    rcases label_cases numbered with ⟨i, hit, _⟩ | ⟨e, _, exitIndex, rfl⟩
    · rw [miss] at hit
      cases hit
    · refine ⟨e.val, ?_, ?_⟩
      · rw [numberExit, number, exitIndex]
        exact Part.mem_some _
      · have outside : graph.blocks.length ≤ (Fin.natAdd graph.blocks.length e).val := by simp
        simpa using Follow.exit (instr := instr prim) (env := env) (blocks := blockCode) outside
  | @more start next final stepped tail ih =>
    rcases label_cases numbered with ⟨i, hit, rfl⟩ | ⟨e, miss, _, _⟩
    · obtain ⟨j, nextNumbered⟩ := step_numbered prim graph exits captures accepted stepped
      have nextMem : (j.val, next.2) ∈ number index next :=
        mem_number.mpr ⟨j, nextNumbered, rfl⟩
      have blockEval := (step_iff prim graph exits captures accepted start.1 i hit
        store env start.2 j.val next.2).mp ((mem_continue index).mpr ⟨next, stepped, nextMem⟩)
      obtain ⟨out, observed, followed⟩ := ih nextNumbered
      exact ⟨out, observed, .step i.isLt blockEval followed⟩
    · simp [CFG.Cyclic.stepSSA, lookup_index, miss, Part.mem_some_iff] at stepped

omit [DecidableEq V] [DecidableEq K] in
private theorem runs_of_follow {count : Nat} {code : Fin count → LambdaSSA.Region F}
    {step : (K × Value α) → Part ((K × Value α) ⊕ (K × Value α))}
    {encode observe : K × Value α → Part (Nat × Value α)}
    (exit : ∀ {start : K × Value α} {slot : Nat} {arg : Value α},
      count ≤ slot → (slot, arg) ∈ encode start →
      ∃ final, Sum.inl final ∈ step start ∧ (slot - count, arg) ∈ observe final)
    (transfer : ∀ {start : K × Value α} {slot next : Nat} {arg result : Value α} {s t : Unit}
      (inside : slot < count), (slot, arg) ∈ encode start →
      Eval (instr prim) (extend env arg) (code ⟨slot, inside⟩) s next result t →
      ∃ jump, Sum.inr jump ∈ step start ∧ (next, result) ∈ encode jump)
    {first out : Nat} {current value : Value α} {s t : Unit}
    (follow : Follow (instr prim) env code first current s out value t) :
    ∀ {start : K × Value α}, (first, current) ∈ encode start →
      ∃ final, Runs step start final ∧ (out, value) ∈ observe final := by
  induction follow using Follow.rec (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | exit outside =>
    intro start numbered
    obtain ⟨final, stopped, observed⟩ := exit outside numbered
    exact ⟨final, .done stopped, observed⟩
  | step inside evaluated _ _ ih =>
    intro start numbered
    obtain ⟨jump, stepped, nextNumbered⟩ := transfer inside numbered evaluated
    obtain ⟨final, tail, observed⟩ := ih exit transfer nextNumbered
    exact ⟨final, .more stepped tail, observed⟩
  | _ => trivial

private theorem runs_of_numbered_follow (accepted : elaborate graph exits captures = some target)
    {first out : Nat} {current value : Value α}
    (follow : Follow (instr prim) env blockCode first current () out value ()) :
    ∀ {start : K × Value α}, (first, current) ∈ number index start →
      ∃ final, Runs namedStep start final ∧ (out, value) ∈ numberExit exits final := by
  refine runs_of_follow (step := namedStep) ?_ ?_ follow
  · intro start pos arg outside numbered
    obtain ⟨slot, numberEq, same⟩ := mem_number.mp numbered
    rcases label_cases numberEq with ⟨i, _, rfl⟩ | ⟨e, miss, exitIndex, rfl⟩
    · simp only [Fin.val_castAdd, Prod.mk.injEq] at same
      have inside := i.isLt
      omega
    · refine ⟨start, step_done.mpr ⟨miss, rfl⟩, ?_⟩
      rw [numberExit, number, exitIndex, Part.mem_some_iff]
      simp only [Fin.val_natAdd, Prod.mk.injEq] at same ⊢
      exact ⟨by omega, same.2.symm⟩
  · intro start pos next arg result s t inside numbered evaluated
    cases s
    cases t
    obtain ⟨slot, numberEq, same⟩ := mem_number.mp numbered
    rcases label_cases numberEq with ⟨i, hit, rfl⟩ | ⟨e, _, _, rfl⟩
    · simp only [Fin.val_castAdd, Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      have numberedStep := (step_iff prim graph exits captures accepted start.1 i hit
        store env start.2 _ _).mpr evaluated
      exact (mem_continue index).mp numberedStep
    · simp only [Fin.val_natAdd, Prod.mk.injEq] at same
      omega

theorem run_iff (accepted : elaborate graph exits captures = some target)
    (inputs : ∀ i : Fin n, env i.val = store (captures i))
    (out : Nat) (value : Value α) :
    (out, value) ∈ (CFG.Cyclic.runSSA (model prim) graph store >>= numberExit exits) ↔
      Eval (instr prim) env target.erase () out value () := by
  simp only [CFG.Cyclic.runSSA, Part.bind_eq_bind, Part.bind_assoc, Part.mem_bind_iff,
    Silmaril.Elgot.Part.mem_iter_iff]
  constructor
  · rintro ⟨initial, entered, final, run, observed⟩
    obtain ⟨i, numberEq⟩ := entry_numbered prim graph exits captures accepted entered
    have numbered : (i.val, initial.2) ∈ number index initial :=
      mem_number.mpr ⟨i, numberEq, rfl⟩
    obtain ⟨exit, reached, followed⟩ := follow_of_runs (env := env) accepted run numberEq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Part.mem_unique observed reached)
    exact .cfg ((entry_iff prim graph exits captures accepted store env inputs _ _).mp
      (Part.mem_bind entered numbered)) followed
  · intro run
    cases run with
    | cfg entry follow =>
      obtain ⟨initial, entered, numbered⟩ := Part.mem_bind_iff.mp
        ((entry_iff prim graph exits captures accepted store env inputs _ _).mpr entry)
      obtain ⟨final, ran, observed⟩ := runs_of_numbered_follow accepted follow numbered
      exact ⟨initial, entered, final, ran, observed⟩

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat
