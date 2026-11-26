module

public import Silmaril.SSA.SeaOfNodes.Loop.Denotation
import Silmaril.Semantics.Elgot.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.Proofs

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open RVSDG (Locals Port Tuple Wires extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data}
variable {g : Graph Op inputs carried entrySigs headerSigs out} {m : Model.{u, v, w} Op}
variable {input : Tuple (Val m.value) (dataPorts inputs)}
variable {old : Tuple (Val m.value) (dataPorts carried)} {result : sortValue m.value out}

private theorem get_map {T : Type u} {F : T → Type v} {G : T → Type w}
    (f : ∀ t, F t → G t) {ts : List T} {t : T} (xs : Tuple F ts) (p : Port ts t) :
    (xs.map f).get p = f t (xs.get p) := by
  induction p with
  | head => cases xs; rfl
  | tail _ ih => cases xs with | cons _ rest => exact ih rest

theorem latch_get (g : Graph Op inputs carried entrySigs headerSigs out)
    (m : Model.{u, v, w} Op) (edge : Incoming)
    (args : Tuple (Val m.value) (edge.select (dataPorts inputs) (headerPorts inputs carried)))
    (locals : Locals (Val m.value) (extend [] (edge.select entrySigs headerSigs)))
    {t : Ty Data} (port : Port (dataPorts carried) t) :
    (g.latch m edge args locals).get port =
      Diamond.read m ((g.phiInputs edge).get port) args locals := by
  unfold Graph.latch Wires.read
  rw [get_map]
  rfl

private theorem evalFrom_sound {budget : Nat} (h : g.evalFrom m input budget old = some result) :
    ∃ count ≤ budget, g.ReturnsAfter m input count old result := by
  induction budget generalizing old with
  | zero =>
    cases step : g.step m input old with
    | inl value =>
      have eq : value = result := Option.some.inj (by simpa only [Graph.evalFrom, step] using h)
      exact ⟨0, Nat.le_refl _, .exit (step.trans (congrArg Sum.inl eq))⟩
    | inr next => simp [Graph.evalFrom, step] at h
  | succ budget ih =>
    cases step : g.step m input old with
    | inl value =>
      have eq : value = result := Option.some.inj (by simpa only [Graph.evalFrom, step] using h)
      exact ⟨0, Nat.zero_le _, .exit (step.trans (congrArg Sum.inl eq))⟩
    | inr next =>
      obtain ⟨count, bound, run⟩ := ih (by simpa only [Graph.evalFrom, step] using h)
      exact ⟨count + 1, Nat.succ_le_succ bound, .backedge step run⟩

private theorem evalFrom_complete {count : Nat} (run : g.ReturnsAfter m input count old result)
    {budget : Nat} (bound : count ≤ budget) : g.evalFrom m input budget old = some result := by
  induction run generalizing budget with
  | exit taken => cases budget <;> simp [Graph.evalFrom, taken]
  | backedge taken _ ih =>
    cases budget with
    | zero => exact False.elim (Nat.not_succ_le_zero _ bound)
    | succ budget => simpa only [Graph.evalFrom, taken] using ih (Nat.le_of_succ_le_succ bound)

theorem evalBackedges_eq_some_iff (g : Graph Op inputs carried entrySigs headerSigs out)
    (m : Model.{u, v, w} Op) (budget : Nat) (input : Tuple (Val m.value) (dataPorts inputs))
    (result : sortValue m.value out) :
    g.evalBackedges m budget input = some result ↔
      ∃ count ≤ budget, g.ReturnsAfter m input count (g.initial m input) result :=
  ⟨evalFrom_sound, fun ⟨_, bound, run⟩ => evalFrom_complete run bound⟩

theorem returns_iff_evalBackedges (g : Graph Op inputs carried entrySigs headerSigs out)
    (m : Model.{u, v, w} Op) (input : Tuple (Val m.value) (dataPorts inputs))
    (result : sortValue m.value out) :
    g.Returns m input result ↔ ∃ budget, g.evalBackedges m budget input = some result := by
  constructor
  · rintro ⟨count, run⟩
    exact ⟨count, evalFrom_complete run (Nat.le_refl count)⟩
  · rintro ⟨_, eval⟩
    obtain ⟨count, _, run⟩ := evalFrom_sound eval
    exact ⟨count, run⟩

private theorem mem_lifted_step
    (outcome : sortValue m.value out ⊕ Tuple (Val m.value) (dataPorts carried)) :
    outcome.map (ULift.up.{u}) id ∈ Part.some ((g.step m input old).map (ULift.up.{u}) id) ↔
      g.step m input old = outcome := by
  cases outcome <;> cases g.step m input old <;> simp [Part.mem_some_iff, eq_comm]

private theorem runs_to_returns {lifted : ULift.{u} (sortValue m.value out)}
    (run : Silmaril.Elgot.Part.Runs
      (fun state => Part.some ((g.step m input state).map (ULift.up.{u}) id)) old lifted) :
    ∃ count, g.ReturnsAfter m input count old lifted.down := by
  induction run with
  | @done start value taken =>
    exact ⟨0, .exit ((mem_lifted_step (old := start) (.inl value.down)).mp taken)⟩
  | more taken _ ih =>
    obtain ⟨count, run⟩ := ih
    exact ⟨count + 1, .backedge ((mem_lifted_step (.inr _)).mp taken) run⟩

private theorem returns_to_runs {count : Nat} (run : g.ReturnsAfter m input count old result) :
    Silmaril.Elgot.Part.Runs (fun state => Part.some ((g.step m input state).map (ULift.up.{u}) id))
      old (ULift.up result) := by
  induction run with
  | @exit start value taken =>
    exact .done ((mem_lifted_step (old := start) (.inl value)).mpr taken)
  | backedge taken _ ih => exact .more ((mem_lifted_step (.inr _)).mpr taken) ih

theorem returns_iff_mem_denote (g : Graph Op inputs carried entrySigs headerSigs out)
    (m : Model.{u, v, w} Op) (input : Tuple (Val m.value) (dataPorts inputs))
    (result : sortValue m.value out) :
    g.Returns m input result ↔ result ∈ g.denote m input := by
  rw [Graph.denote, Part.mem_map_iff]
  constructor
  · rintro ⟨_, run⟩
    exact ⟨ULift.up result, (Silmaril.Elgot.Part.mem_run_iff _ _ _).mpr (returns_to_runs run), rfl⟩
  · rintro ⟨lifted, mem, rfl⟩
    exact runs_to_returns ((Silmaril.Elgot.Part.mem_run_iff _ _ lifted).mp mem)

theorem not_returns_of_backedge_invariant
    (invariant : Tuple (Val m.value) (dataPorts carried) → Prop)
    (initial : invariant (g.initial m input))
    (continues : ∀ old, invariant old → ∃ next, g.step m input old = .inr next ∧ invariant next) :
    ¬ g.Returns m input result := by
  have excludes {old count} (run : g.ReturnsAfter m input count old result) :
      invariant old → False := by
    induction run with
    | exit taken =>
      intro holds
      obtain ⟨_, next, _⟩ := continues _ holds
      cases taken.symm.trans next
    | backedge taken _ ih =>
      intro holds
      obtain ⟨_, next, nextHolds⟩ := continues _ holds
      exact ih (Sum.inr.inj (next.symm.trans taken) ▸ nextHolds)
  rintro ⟨_, run⟩
  exact excludes run initial

end Silmaril.SSA.SeaOfNodes.Loop.Proofs
