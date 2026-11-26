module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Infinite.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Reflection.Thms
import Silmaril.Semantics.Elgot.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Semantics
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.WholeRun
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Semantics

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Flat)
open LambdaSSA.Semantics (Diverges Env extend)
open LambdaSSA.Semantics.Region (Eval)
open LetCase.LocallyNameless (Tm)

universe u v w x

section Isotope

variable {F : Type v} {α : Type w} {σ : Type x}
variable {blocks exits n : Nat} {target : FiniteCFG F blocks exits n}
variable {env : Env α} {instr : F → Value α → σ → Value α → σ → Prop} {start : σ}

private abbrev Transfer (blocks : Nat) (α : Type w) (σ : Type x) :=
  Fin blocks × Value α × σ

private def InternalPath (instr : F → Value α → σ → Value α → σ → Prop)
    (env : Env α) (target : FiniteCFG F blocks exits n) (start : σ) : Prop :=
  ∃ path : Nat → Transfer blocks α σ,
    Eval instr env target.entry.erase start (path 0).1.val (path 0).2.1 (path 0).2.2 ∧
    ∀ i, Eval instr (extend env (path i).2.1) (target.block (path i).1).erase
      (path i).2.2 (path (i + 1)).1.val (path (i + 1)).2.1 (path (i + 1)).2.2

private theorem flat_not_diverges {labels : Nat} {r : Flat F labels n} :
    ¬ Diverges instr (.region env r.erase start) := by
  induction r generalizing env start with
  | br => intro h; cases h.unfold
  | let₁ _ _ ih =>
    intro h
    cases h.unfold with
    | let₁ _ tail => exact ih tail
  | let₂ _ _ ih =>
    intro h
    cases h.unfold with
    | let₂ _ tail => exact ih tail
  | case _ _ _ ihl ihr =>
    intro h
    cases h.unfold with
    | case_inl _ tail => exact ihl tail
    | case_inr _ tail => exact ihr tail

local notation "code" => (fun j => Flat.erase (target.block j))
local notation "pending" => (fun (p : Nat × Value α × σ) =>
  LambdaSSA.Semantics.Config.follow env code (Prod.fst p) (Prod.fst (Prod.snd p)) (Prod.snd (Prod.snd p)))

private theorem follow_next {p : Nat × Value α × σ}
    (div : Diverges instr (pending p)) :
    ∃ (inside : p.1 < blocks) (q : Nat × Value α × σ),
      Eval instr (extend env p.2.1) (target.block ⟨p.1, inside⟩).erase p.2.2 q.1 q.2.1 q.2.2 ∧
      Diverges instr (pending q) := by
  cases div.unfold with
  | follow_body _ tail => exact (flat_not_diverges tail).elim
  | follow_next inside step rest =>
    rename_i next state value
    exact ⟨inside, (next, value, state), step, rest⟩

private theorem internal_path_iff :
    InternalPath instr env target start ↔ Diverges instr (.region env target.erase start) := by
  constructor
  · rintro ⟨path, entered, steps⟩
    refine .fold (.cfg_follow entered (Diverges.coinduct (fun config =>
      ∃ i, config = pending ((path i).1.val, (path i).2)) ?_ ⟨0, rfl⟩))
    rintro _ ⟨i, rfl⟩
    exact .follow_next (path i).1.isLt (steps i) ⟨i + 1, rfl⟩
  · intro div
    cases div.unfold with
    | cfg_entry head => exact (flat_not_diverges head).elim
    | cfg_follow entered follows =>
      rename_i state label value
      let State := {p : Nat × Value α × σ // Diverges instr (pending p)}
      have next (p : State) : ∃ q : State, ∃ inside : p.val.1 < blocks,
          Eval instr (extend env p.val.2.1) (target.block ⟨p.val.1, inside⟩).erase
            p.val.2.2 q.val.1 q.val.2.1 q.val.2.2 := by
        obtain ⟨inside, q, executed, continued⟩ := follow_next p.property
        exact ⟨⟨q, continued⟩, inside, executed⟩
      -- Each selected successor carries its own divergent continuation.
      let trace : Nat → State := Nat.rec ⟨(label, value, state), follows⟩ fun _ p => Classical.choose (next p)
      let path (i : Nat) : Transfer blocks α σ :=
        (⟨(trace i).val.1, (Classical.choose_spec (next (trace i))).choose⟩, (trace i).val.2)
      exact ⟨path, entered, fun i => (Classical.choose_spec (next (trace i))).choose_spec⟩

theorem flat_diverges_iff_of_eval {G : Type u} {m : Nat}
    {other : FiniteCFG G blocks exits m} {env' : Env α}
    {instr' : G → Value α → σ → Value α → σ → Prop}
    (entry : ∀ out value finish, Eval instr env target.entry.erase start out value finish ↔
      Eval instr' env' other.entry.erase start out value finish)
    (blocks : ∀ i current state out value finish,
      Eval instr (extend env current) (target.block i).erase state out value finish ↔
        Eval instr' (extend env' current) (other.block i).erase state out value finish) :
    Diverges instr (.region env target.erase start) ↔ Diverges instr' (.region env' other.erase start) := by
  rw [← internal_path_iff, ← internal_path_iff]
  constructor <;> rintro ⟨path, entered, steps⟩
  · exact ⟨path, (entry _ _ _).mp entered, fun i => (blocks _ _ _ _ _ _).mp (steps i)⟩
  · exact ⟨path, (entry _ _ _).mpr entered, fun i => (blocks _ _ _ _ _ _).mpr (steps i)⟩

variable {τ : Type u} {β : BoundCtx τ n} {input : Tm Empty F 0}
  {closed : FiniteCFG F blocks exits 0} {ambient : Env α}

theorem closure_diverges_iff (h : Capture.Closes β input target closed)
    (packet : ∀ v state, LambdaSSA.Semantics.Tm.Eval instr ambient (Morphism.CaseSSA.erase input)
      start v state ↔ v = Capture.packEnv n env ∧ state = start) :
    Diverges instr (.region ambient closed.erase start) ↔ Diverges instr (.region env target.erase start) :=
  flat_diverges_iff_of_eval (fun _ _ _ => Capture.entry_eval_iff h packet)
    (fun i current _ _ _ _ => Capture.block_eval_iff h i current)

end Isotope

section Named

variable {V K F α : Type u} {n : Nat} [DecidableEq V] [DecidableEq K]
variable {prim : F → Value α → Part (Value α)} {graph : CFG V K F} {exits : List K}
variable {captures : Fin n → V} {store : V → Value α} {env : Env α}
variable {target : FiniteCFG F graph.blocks.length exits.length n}

local notation "index" => labelIndex graph.blocks exits
local notation "namedStep" => CFG.Cyclic.stepSSA (model prim) graph.blocks store
local notation "findBlock" => (fun label => graph.blocks.findFinIdx? (fun item => label == Prod.fst item))

theorem runSSA_eq_none (infinite : InfiniteRun prim graph store) :
    CFG.Cyclic.runSSA (model prim) graph store = Part.none := by
  obtain ⟨path, entered, steps⟩ := infinite
  have incompatible {first final : K × Value α}
      (finite : Silmaril.Elgot.Part.Runs namedStep first final) :
      ∀ i, first = path i → False := by
    induction finite with
    | done finished =>
      rintro i rfl
      cases Part.mem_unique finished (steps i)
    | more stepped _ ih =>
      rintro i rfl
      exact ih (i + 1) (Sum.inr.inj (Part.mem_unique stepped (steps i)))
  apply Part.eq_none_iff.mpr
  intro result ran
  obtain ⟨first, entry, returned⟩ := Part.mem_bind_iff.mp ran
  cases Part.mem_unique entry entered
  exact incompatible ((Silmaril.Elgot.Part.mem_iter_iff _ _ _).mp returned) 0 rfl

private theorem step_has_block {current next : K × Value α}
    (h : Sum.inr next ∈ namedStep current) : ∃ i, findBlock current.1 = some i := by
  cases hit : findBlock current.1 with
  | none => simp [CFG.Cyclic.stepSSA, lookup_index, hit, Part.mem_some_iff] at h
  | some i => exact ⟨i, rfl⟩

private theorem flat_path_of_named (accepted : elaborate graph exits captures = some target)
    (inputs : ∀ i : Fin n, env i.val = store (captures i)) (run : InfiniteRun prim graph store) :
    InternalPath (instr prim) env target () := by
  obtain ⟨path, entered, stepped⟩ := run
  have hit (i : Nat) := step_has_block (stepped i)
  let slot (i : Nat) := Classical.choose (hit i)
  have found (i : Nat) : graph.blocks.findFinIdx? (fun item => (path i).1 == item.1) = some (slot i) :=
    Classical.choose_spec (hit i)
  have numbered (i : Nat) : ((slot i).val, (path i).2) ∈ number index (path i) := by
    refine mem_number.mpr ⟨(slot i).castAdd exits.length, ?_, rfl⟩
    unfold labelIndex
    rw [found i]
  refine ⟨fun i => (slot i, (path i).2, ()), ?_, ?_⟩
  · exact (entry_iff prim graph exits captures accepted store env inputs _ _).mp
      (Part.mem_bind entered (numbered 0))
  · intro i
    exact (step_iff prim graph exits captures accepted (path i).1 (slot i)
      (found i) store env (path i).2 _ _).mp
      ((mem_continue index).mpr ⟨_, stepped i, numbered (i + 1)⟩)

private theorem named_of_flat_path (accepted : elaborate graph exits captures = some target)
    (inputs : ∀ i : Fin n, env i.val = store (captures i))
    (run : InternalPath (instr prim) env target ()) : InfiniteRun prim graph store := by
  obtain ⟨path, entry, stepped⟩ := run
  -- Each named transfer must encode to its position in the given Isotope path.
  let Position (i : Nat) := {p : K × Value α // ((path i).1.val, (path i).2.1) ∈ number index p}
  obtain ⟨initial, entered, numbered⟩ := Part.mem_bind_iff.mp
    ((entry_iff prim graph exits captures accepted store env inputs _ _).mpr (by
      simpa only [show (path 0).2.2 = () from Subsingleton.elim _ _] using entry))
  have next (i : Nat) (p : Position i) : ∃ q : Position (i + 1), Sum.inr q.val ∈ namedStep p.val := by
    obtain ⟨slot, numberEq, same⟩ := mem_number.mp p.property
    rcases label_cases numberEq with ⟨j, hit, rfl⟩ | ⟨e, _, _, rfl⟩
    · have blockEq : j = (path i).1 := Fin.ext (congrArg Prod.fst same)
      have argEq : p.val.2 = (path i).2.1 := congrArg Prod.snd same
      have evaluated := stepped i
      rw [← blockEq, ← argEq] at evaluated
      have continued := (step_iff prim graph exits captures accepted p.val.1 j hit
        store env p.val.2 _ _).mpr (by
          simpa only [show (path i).2.2 = () from Subsingleton.elim _ _,
            show (path (i + 1)).2.2 = () from Subsingleton.elim _ _] using evaluated)
      obtain ⟨q, step, numbered⟩ := (mem_continue index).mp continued
      exact ⟨⟨q, numbered⟩, step⟩
    · have bound := (path i).1.isLt
      have eq := congrArg Prod.fst same
      simp only [Fin.val_natAdd] at eq
      omega
  let lifted : (i : Nat) → Position i := Nat.rec ⟨initial, numbered⟩
    fun i p => Classical.choose (next i p)
  exact ⟨fun i => (lifted i).val, entered, fun i => Classical.choose_spec (next i (lifted i))⟩

theorem infinite_run_iff (accepted : elaborate graph exits captures = some target)
    (inputs : ∀ i : Fin n, env i.val = store (captures i)) :
    InfiniteRun prim graph store ↔ Diverges (instr prim) (.region env target.erase ()) :=
  ⟨fun run => internal_path_iff.mp (flat_path_of_named accepted inputs run),
    fun div => named_of_flat_path accepted inputs (internal_path_iff.mpr div)⟩

end Named

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat
