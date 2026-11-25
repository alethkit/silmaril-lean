module

public import Silmaril.Wasm.Institution.Operational.Division.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Division.Proofs

open Silmaril.Semantics.SOS Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile}

@[simp] private theorem admitted_nil : AdmittedCode [] := fun _ h => nomatch h

@[simp] private theorem admitted_cons {a : Admin} {code : List Admin} :
    AdmittedCode (a :: code) ↔ Allowed a ∧ AdmittedCode code := by
  simp [AdmittedCode]

@[simp] private theorem admitted_append {a b : List Admin} :
    AdmittedCode (a ++ b) ↔ AdmittedCode a ∧ AdmittedCode b := by
  exact List.forall_mem_append

@[simp] private theorem admitted_vals (vs : List Val) : AdmittedCode (vals vs) := by
  intro a h
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp h
  exact .value v

@[simp] private theorem allowed_const (t : IntType) (x : IntValue t) : Allowed (intConst t x) :=
  .value (.num ⟨.int t, x⟩)

@[simp] private theorem allowed_div (t : IntType) (sign : Signedness) : Allowed (divOp t sign) :=
  .division t sign

@[simp] private theorem allowed_trap : Allowed .trap := .trap
@[simp] private theorem allowed_nop : Allowed (.plain .nop) := .nop

private theorem noThrowRef {a : Admin} (h : Allowed a) : a ≠ .plain .throwRef := by
  cases h with
  | value v =>
    intro eq
    have hv := congrArg Admin.val? eq
    change v.toAdmin.val? = none at hv
    simp at hv
  | _ => intro eq; cases eq

private theorem division_result (t : IntType) (sign : Signedness) (x y : IntValue t) :
    intBinOp t (.div sign) x y =
      if y = 0 then .error .divideByZero
      else if Overflows t sign x y then .error .overflow
      else .ok (quotient t sign x y) := by
  cases sign <;> simp [intBinOp, quotient, Overflows]

private theorem overflow_divisor (t : IntType) : (-1 : IntValue t) ≠ 0 := by
  cases t <;> decide

theorem derives_admitted {s t : Config H} (h : DerivesEdge s t) :
    Admitted s ∧ Admitted t := by
  change Derives (presentation H).rules (s, t) at h
  have support : ∀ {j : Judgment H}, Derives (presentation H).rules j →
      Admitted j.1 ∧ Admitted j.2 := by
    intro j hj
    induction hj with
    | apply member _ ih =>
      change RuleInstance H _ at member
      cases member with
      | context s f vs before after rest _ tail =>
        have inner := ih (codeEdge s f before after) (by simp)
        simpa [Admitted, codeEdge, tail] using inner
      | trap _ _ _ _ _ tail =>
        simp [Admitted, codeEdge, tail]
      | _ => simp [Admitted, codeEdge]
  exact support h

theorem derives_sound {s t : Config H} (h : DerivesEdge s t) : Step P noHost s t := by
  change Derives (presentation H).rules (s, t) at h
  have sound : ∀ {j : Judgment H}, Derives (presentation H).rules j → Step P noHost j.1 j.2 := by
    intro j hj
    induction hj with
    | apply member _ ih =>
      change RuleInstance H _ at member
      cases member with
      | divide _ _ ty sign x y hy hov =>
        exact .numeric (.intBinOp (by rw [division_result, ite_eq_right hy, ite_eq_right hov]))
      | zero _ _ ty sign x =>
        exact .numeric (.intBinOpTrap (intBinOp_div_zero ty sign x))
      | overflow _ _ ty =>
        exact .numeric (.intBinOpTrap (e := .overflow) (by
          rw [division_result, ite_eq_right (overflow_divisor ty), ite_eq_left ⟨rfl, rfl, rfl⟩]))
      | nop => exact .parametric .nop
      | trap _ _ _ _ hne _ => exact .trapInstrs hne
      | context s f _ before after _ hne _ =>
        exact .ctxtInstrs (ih (codeEdge s f before after) (by simp)) hne
  exact sound h

private theorem useFact {j : Judgment H} (rule : RuleInstance H ⟨[], j⟩) :
    Derives (presentation H).rules j :=
  Derives.apply (R := (presentation H).rules) (r := ⟨[], j⟩) rule (fun _ h => nomatch h)

private theorem useContext (s : Store H) (f : Frame) (vs : List Val)
    {before after rest : List Admin} (hr : AdmittedCode rest)
    (h : Derives (presentation H).rules (codeEdge s f before after)) :
    Derives (presentation H).rules (codeEdge s f (vals vs ++ before ++ rest)
      (vals vs ++ after ++ rest)) := by
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · refine Derives.apply
      (r := ⟨[codeEdge s f before after], codeEdge s f _ _⟩)
      (RuleInstance.context s f vs before after rest hne hr) ?_
    intro j hj
    rwa [List.mem_singleton.mp hj]
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    simpa using h

private theorem numeric_readback (s : Store H) (f : Frame) {before after : List Admin}
    (step : NumericStep P before after) {ty : IntType} {sign : Signedness}
    (last : before.getLast? = some (divOp ty sign)) :
    Derives (presentation H).rules (codeEdge s f before after) := by
  cases step <;> simp [divOp] at last
  case intBinOp t op x y z out =>
    obtain ⟨rfl, rfl⟩ := last
    rw [division_result] at out
    split at out
    · contradiction
    split at out
    · contradiction
    rename_i hy hov
    cases out
    exact useFact (.divide s f t sign x y hy hov)
  case intBinOpTrap t op x y e out =>
    obtain ⟨rfl, rfl⟩ := last
    by_cases hy : y = 0
    · subst y
      exact useFact (.zero s f t sign x)
    by_cases hov : Overflows t sign x y
    · obtain ⟨rfl, rfl, rfl⟩ := hov
      exact useFact (.overflow s f t)
    · rw [division_result, ite_eq_right hy, ite_eq_right hov] at out
      contradiction

private theorem parametric_readback (s : Store H) (f : Frame) {before after : List Admin}
    (step : ParametricStep before after) (last : before.getLast? = some (.plain .nop)) :
    Derives (presentation H).rules (codeEdge s f before after) := by
  cases step <;> simp_all
  exact useFact (.nop s f)

private theorem head_readback {s : Store H} {f : Frame} {args : List Val} {op : Admin}
    {next : Config H} (step : Head P s f args op next) (supported : Allowed op) :
    ∃ out, next = ⟨s, f, out⟩ ∧
      Derives (presentation H).rules (codeEdge s f (vals args ++ [op]) out) := by
  cases supported with
  | value v =>
    have none := step.good.val_none
    simp at none
  | division ty sign =>
    have fam : FamRel P .numeric s f (vals args ++ [divOp ty sign]) next :=
      step.fam_inv (by change Fam.numeric ≠ .control; decide)
    obtain ⟨out, numeric, rfl⟩ := fam
    exact ⟨out, rfl, numeric_readback s f numeric (ty := ty) (sign := sign) (by simp)⟩
  | nop =>
    have fam : FamRel P .parametric s f (vals args ++ [.plain .nop]) next :=
      step.fam_inv (by decide)
    obtain ⟨out, parametric, rfl⟩ := fam
    exact ⟨out, rfl, parametric_readback s f parametric (by simp)⟩
  | trap => exact (step.good.ne_trap rfl).elim

theorem step_readback {s t : Config H} (supported : Admitted s) (step : Step P noHost s t) :
    DerivesEdge s t := by
  rcases s with ⟨s, f, code⟩
  change AdmittedCode code at supported
  rcases Silmaril.Wasm.SingleThreaded.Det.Step.decomp step with head | bubble
  · obtain ⟨saved, args, op, rest, next, rfl, hh, rfl⟩ := head
    obtain ⟨out, rfl, rule⟩ := head_readback hh (supported op (by simp))
    have hr : AdmittedCode rest := fun a member => supported a (by simp [member])
    simpa [codeEdge, List.append_assoc] using useContext s f saved hr rule
  · obtain ⟨saved, discarded, skipped, rest, nonempty, ⟨_, rfl, rfl⟩ | ⟨tag, _, rfl, _⟩⟩ :=
      fnv_bubble bubble
    · have hTail : AdmittedCode skipped ∧ AdmittedCode rest := by simpa using supported
      have rule := useFact (RuleInstance.trap s f discarded skipped nonempty hTail.1)
      simpa [codeEdge, vals_append, List.append_assoc] using useContext s f saved hTail.2 rule
    · exact (noThrowRef (supported (.plain .throwRef) (by simp)) rfl).elim

end Silmaril.Wasm.Institution.Operational.Division.Proofs
