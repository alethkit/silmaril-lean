module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Defs
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Replay

public section

namespace Silmaril.Isotope.LetSeq.StraightLine

open LocallyNameless (Derivation Equiv)
open Silmaril.Isotope.Semantics (BoundEnv)
open Silmaril.Semantics.NondeterministicTrace

set_option backward.isDefEq.respectTransparency false

private theorem slot_cases {n : Nat} {β : BoundCtx Types n} {P : Slot (β.snoc Atom) → Prop}
    (zero : P ⟨0, rfl⟩) (succ : ∀ s : Slot β, P ⟨s.1.succ, s.2⟩) :
    ∀ s, P s := by
  rintro ⟨i, h⟩
  revert h
  exact Fin.cases (fun _ => zero) (fun j h => succ ⟨j, h⟩) i

theorem separating_snoc_proof {n : Nat} {β : BoundCtx Types n} {ρ : BoundEnv Value β} {fresh : Nat}
    (h : Separating ρ fresh) : Separating (ρ.snoc (A := Atom) fresh) (fresh + 1) where
  below := slot_cases (Nat.lt_succ_self _) (fun s => Nat.lt_succ_of_lt (h.below s))
  injective := by
    intro x
    induction x using slot_cases with
    | zero =>
      intro y
      induction y using slot_cases with
      | zero => exact fun _ => rfl
      | succ y =>
        intro eq
        have neq := Nat.ne_of_lt (h.below y)
        exact (neq eq.symm).elim
    | succ x =>
      intro y
      induction y using slot_cases with
      | zero =>
        intro eq
        exact (Nat.ne_of_lt (h.below x) eq).elim
      | succ y =>
        intro eq
        have same := h.injective eq
        cases same
        rfl

private theorem slot_run {n : Nat} {β : BoundCtx Types n} (s : Slot β) (ρ : BoundEnv Value β) :
    run (slotDerivation s) ρ = pure (s.value ρ) := by
  have variableRun (A : Types) (h : β.get s.1 = A) :
      run (cast (congrArg (Derivation Request Γ₀ β (.bv s.1)) h) .bv) ρ =
        pure (cast (congrArg Value h) (ρ s.1)) := by
    cases h
    rfl
  exact variableRun Atom s.2

theorem run_request_proof {n : Nat} {β : BoundCtx Types n} {body : Term (n + 2)}
    (f : Request) (x y : Slot β) (rest : Canonical ((β.snoc Atom).snoc Atom) body)
    (ρ : BoundEnv Value β) :
    run (canonicalDerivation (.request f x y rest)) ρ =
      model.eval f (x.value ρ, y.value ρ) >>= fun ab =>
        run (canonicalDerivation rest) ((ρ.snoc (A := Atom) ab.1).snoc (A := Atom) ab.2) := by
  have left := slot_run x ρ
  have right := slot_run y ρ
  unfold run at left right
  simp only [canonicalDerivation, requestDerivation, run, Derivation.denote, left, right, pure_bind]
  rfl

theorem request_mem_proof {A : Type} {f : Request} {arg : Nat × Nat} {k : Nat × Nat → Trace A}
    {z : A} {w : Log} :
    (z, w) ∈ (model.eval f arg >>= k).outcomes ↔
      ∃ reply tail, (z, tail) ∈ (k reply).outcomes ∧ FreeMonoid.of ⟨f, arg, reply⟩ * tail = w := by
  rw [Finite.mem_bind]
  constructor
  · rintro ⟨a, u, v, ⟨reply, hr⟩, hv, rfl⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    exact ⟨reply, v, hv, rfl⟩
  · rintro ⟨reply, tail, h, rfl⟩
    exact ⟨reply, _, tail, ⟨reply, rfl⟩, h, rfl⟩

private theorem log_cons_inj {e f : Event} {l r : Log}
    (h : FreeMonoid.of e * l = FreeMonoid.of f * r) : e = f ∧ l = r := by
  have words : e :: l.toList = f :: r.toList := congrArg FreeMonoid.toList h
  exact ⟨(List.cons.inj words).1, FreeMonoid.ext (List.cons.inj words).2⟩

private theorem log_cons_ne_one (e : Event) (l : Log) : FreeMonoid.of e * l ≠ 1 := by
  intro h
  have words : e :: l.toList = [] := congrArg FreeMonoid.toList h
  cases words

/-- Pick a legal run with two fresh atoms at each request. The observation
records those choices, so a second program matching it must use them too. -/
private def sample {n : Nat} {β : BoundCtx Types n} {t : Term n}
    (w : Canonical β t) (ρ : BoundEnv Value β) (fresh : Nat) : Nat × Log :=
  match w with
  | .ret x => (x.value ρ, 1)
  | .request f x y rest =>
    let ab := (fresh, fresh + 1)
    let suffix := sample rest ((ρ.snoc (A := Atom) ab.1).snoc (A := Atom) ab.2) (fresh + 2)
    (suffix.1, FreeMonoid.of ⟨f, (x.value ρ, y.value ρ), ab⟩ * suffix.2)

private theorem sample_mem {n : Nat} {β : BoundCtx Types n} {t : Term n}
    (w : Canonical β t) (ρ : BoundEnv Value β) (fresh : Nat) :
    sample w ρ fresh ∈ (run (canonicalDerivation w) ρ).outcomes := by
  induction w generalizing fresh with
  | ret x =>
    change (x.value ρ, 1) ∈ (run (slotDerivation x) ρ).outcomes
    rw [slot_run]
    rfl
  | request f x y rest ih =>
    rw [run_request_proof]
    exact request_mem_proof.mpr ⟨(fresh, fresh + 1), _, ih _ _, rfl⟩

private theorem sample_reflect {n : Nat} {β : BoundCtx Types n} {t : Term n}
    (p : Canonical β t) (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    ∀ {u : Term n} (q : Canonical β u), sample p ρ fresh ∈ (run (canonicalDerivation q) ρ).outcomes → t = u := by
  induction p generalizing fresh with
  | ret x =>
    intro u q h
    cases q with
    | ret y =>
      change (x.value ρ, 1) ∈ (run (slotDerivation y) ρ).outcomes at h
      rw [slot_run] at h
      have same : (x.value ρ, (1 : Log)) = (y.value ρ, 1) := h
      exact congrArg (fun i : Slot _ => LocallyNameless.Tm.bv i.1) (sep.injective (Prod.mk.inj same).1)
    | request f y z rest =>
      rw [run_request_proof] at h
      obtain ⟨reply, tail, _, log⟩ := request_mem_proof.mp h
      exact (log_cons_ne_one _ _ log).elim
  | request f x y rest ih =>
    intro u q h
    cases q with
    | ret z =>
      change sample (.request f x y rest) ρ fresh ∈ (run (slotDerivation z) ρ).outcomes at h
      rw [slot_run] at h
      have eq : sample (.request f x y rest) ρ fresh = (z.value ρ, 1) := h
      exact (log_cons_ne_one _ _ (congrArg Prod.snd eq)).elim
    | request g a b next =>
      rw [run_request_proof] at h
      let ab := (fresh, fresh + 1)
      let extended := (ρ.snoc (A := Atom) ab.1).snoc (A := Atom) ab.2
      let suffix := sample rest extended (fresh + 2)
      have mem : (suffix.1, FreeMonoid.of ⟨f, (x.value ρ, y.value ρ), ab⟩ * suffix.2) ∈ _ := h
      obtain ⟨reply, tail, selected, log⟩ := request_mem_proof.mp mem
      obtain ⟨head, tailEq⟩ := log_cons_inj log
      obtain ⟨label, arg, answer⟩ := Event.mk.inj head
      have sameX := sep.injective (Prod.mk.inj arg).1
      have sameY := sep.injective (Prod.mk.inj arg).2
      cases label
      cases sameX
      cases sameY
      cases answer
      cases tailEq
      exact congrArg (LocallyNameless.Tm.let₂ (requestTerm f x.1 y.1))
        (ih extended (fresh + 2) (separating_snoc_proof (separating_snoc_proof sep)) next selected)

theorem canonical_eq_proof {n : Nat} {β : BoundCtx Types n} {t u : Term n}
    (p : Canonical β t) (q : Canonical β u) (ρ : BoundEnv Value β) (fresh : Nat)
    (sep : Separating ρ fresh)
    (h : run (canonicalDerivation p) ρ = run (canonicalDerivation q) ρ) : t = u :=
  sample_reflect p ρ fresh sep q (h ▸ sample_mem p ρ fresh)

end Silmaril.Isotope.LetSeq.StraightLine
