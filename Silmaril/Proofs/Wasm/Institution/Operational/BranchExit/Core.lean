module

public import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Defs
public import Silmaril.Wasm.Institution.Operational.BranchExit.Thms
public import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.SingleThreaded.Determinism.Stuck
public import Silmaril.Wasm.SingleThreaded.Determinism.Head

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.BranchExit.Proofs

open Execution.Core
open Execution.Core.Sim (vals_append_cons_inj)

open SingleThreaded.Det (fnv fnv_cons_of_none)

private abbrev stack (vs : List Execution.Runtime.Value) := vs.map LegacyDivision.liftValue

private theorem arity {ty : Option NumType} {payload : List Execution.Runtime.Value}
    (typed : payload.map Execution.Runtime.Value.type = ty.toList) :
    (stack payload).length = ty.toList.length := by
  simpa using congrArg List.length typed

theorem core_sound {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {ty : Option NumType} {a b : State} (e : Edge ty a b) :
    Step P host (coreConfig s f ty a) (coreConfig s f ty b) := by
  cases invert e with
  | cross n below payload =>
    have crossed := Step.brLabelSucc (P := P) (host := host) (s := s) (f := f) (n := n)
      (cont := []) (vs := stack (below ++ payload)) (l := (⟨1⟩ : LabelIdx)) (rest := []) (by decide)
    have lowered : labelPred (⟨1⟩ : LabelIdx) = ⟨0⟩ := by decide
    simpa only [coreConfig, coreCode, List.append_nil, lowered] using
      (Step.ctxtLabel (n := ty.toList.length) (cont := []) crossed)
  | finish below payload typed =>
    simpa only [coreConfig, coreCode, List.map_append, vals_append, List.append_nil, expression, List.map_nil] using
      (Step.brLabelZero (P := P) (host := host) (s := s) (f := f) (cont := [])
        (l := (⟨0⟩ : LabelIdx)) (vs' := stack below) (vs := stack payload) (rest := [])
        rfl (arity typed))

private def first (code : List Admin) := code.find? (fun a => a.val?.isNone)

@[simp] private theorem first_values (vs : List Val) : first (vals vs) = none := by
  apply List.find?_eq_none.mpr
  intro a member
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp member
  simp [Admin.val?_toAdmin]

@[simp] private theorem first_prefix (vs : List Val) (code : List Admin) :
    first (vals vs ++ code) = first code := by
  change List.find? _ (vals vs ++ code) = _
  rw [List.find?_append]
  change (first (vals vs)).or (first code) = _
  simp

@[simp] private theorem first_head {a : Admin} (tail : List Admin) (ha : a.val? = none) :
    first (a :: tail) = some a := by
  simp [first, ha]

@[simp] private theorem first_throwing (a : Nat) :
    first (throwing a) = some (.plain .throwRef) := by
  change first (vals [.ref (.exn a)] ++ [.plain .throwRef]) = _
  rw [first_prefix]
  rfl

private theorem nested_cannot_exit {outer inner : Nat} {body out : List Admin}
    (h : LabelExit outer [] [.label inner [] body] out) : False := by
  generalize eq : ([.label inner [] body] : List Admin) = before at h
  have head := congrArg first eq
  cases h with
  | returnCall hc =>
    have none := Admin.val?_of_isReturnCallRef hc
    simp only [List.append_assoc, List.singleton_append, first_prefix, first_head _ none] at head
    simp [first, Admin.val?] at head
    cases head
    cases hc
  | _ =>
    try simp only [List.append_assoc, List.singleton_append, first_prefix, first_values, first_throwing] at head
    simp [first, Admin.val?] at head

private theorem label_br_readback {n : Nat} {cont : List Instr} {l : LabelIdx} {vs : List Val} {rest out : List Admin}
    (h : LabelExit n cont (vals vs ++ .plain (.br l) :: rest) out) :
    (∃ below payload, vs = below ++ payload ∧ payload.length = n ∧ l.toNat = 0 ∧ out = vals payload ++ expression cont) ∨
      (0 < l.toNat ∧ out = vals vs ++ [.plain (.br (labelPred l))]) := by
  generalize eq : vals vs ++ .plain (.br l) :: rest = before at h
  have head := congrArg first eq
  cases h with
  | brZero hz hn =>
    rw [List.append_assoc, List.singleton_append, ← vals_append] at eq
    obtain ⟨eqStack, same, _⟩ := vals_append_cons_inj rfl rfl eq
    cases same
    exact .inl ⟨_, _, eqStack, hn, hz, rfl⟩
  | brSucc hp =>
    rw [List.append_assoc, List.singleton_append] at eq
    obtain ⟨rfl, same, _⟩ := vals_append_cons_inj rfl rfl eq
    cases same
    exact .inr ⟨hp, rfl⟩
  | returnCall hc =>
    have noVal := Admin.val?_of_isReturnCallRef hc
    simp only [List.append_assoc, List.singleton_append, first_prefix, first_head _ noVal] at head
    simp [first, Admin.val?] at head
    cases head
    cases hc
  | _ =>
    simp only [List.append_assoc, List.singleton_append, first_prefix, first_values, first_throwing] at head
    simp [first, Admin.val?] at head

theorem core_label_br_zero {n : Nat} {vs : List Val} {rest out : List Admin}
    (pop : LabelExit n [] (vals vs ++ .plain (.br ⟨0⟩) :: rest) out) :
    ∃ scratch results, vs = scratch ++ results ∧ results.length = n ∧ out = vals results := by
  rcases label_br_readback pop with ⟨scratch, results, split, arity, _, eq⟩ | ⟨bad, _⟩
  · exact ⟨scratch, results, split, arity, by simpa [expression] using eq⟩
  · exact (Nat.lt_irrefl 0 bad).elim

theorem core_label_br_cont_iff {H : Type} {P : Numerics.Profile} {s : Store H} {f : Frame}
    {n : Nat} {cont : List Instr} {depth : LabelIdx} {stack : List Val} {rest : List Admin} {dst : Config H} :
    Step P SingleThreaded.Det.noHost ⟨s, f, [.label n cont (vals stack ++ .plain (.br depth) :: rest)]⟩ dst ↔
      (∃ extra payload, stack = extra ++ payload ∧ payload.length = n ∧ depth.toNat = 0 ∧
        dst = ⟨s, f, vals payload ++ expression cont⟩) ∨
      (0 < depth.toNat ∧ dst = ⟨s, f, vals stack ++ [.plain (.br (labelPred depth))]⟩) := by
  constructor
  · intro step
    rcases Step.label_inv step with ⟨_, _, _, move, _⟩ | ⟨_, pop, rfl⟩
    · have first : fnv (vals stack ++ .plain (.br depth) :: rest) =
          (stack, .plain (.br depth) :: rest) := by
        simp [fnv_cons_of_none (a := .plain (.br depth)) rfl]
      exact ((SingleThreaded.Det.not_step_blocked move first) (.inl ⟨_, rfl⟩)).elim
    rcases label_br_readback pop with ⟨extra, payload, split, size, here, rfl⟩ | ⟨outer, rfl⟩
    · exact .inl ⟨extra, payload, split, size, here, rfl⟩
    · exact .inr ⟨outer, rfl⟩
  · rintro (⟨extra, payload, rfl, size, here, rfl⟩ | ⟨outer, rfl⟩)
    · simpa only [vals_append, List.append_assoc, List.singleton_append] using
        (Step.brLabelZero (P := P) (host := SingleThreaded.Det.noHost) (s := s) (f := f) (cont := cont)
          (l := depth) (vs' := extra) (vs := payload) (rest := rest) here size)
    · simpa only [List.append_assoc, List.singleton_append] using
        (Step.brLabelSucc (P := P) (host := SingleThreaded.Det.noHost) (s := s) (f := f) (n := n)
          (cont := cont) (vs := stack) (l := depth) (rest := rest) outer)

theorem core_label_br_iff {H : Type} {P : Numerics.Profile} {s : Store H} {f : Frame}
    {n : Nat} {depth : LabelIdx} {stack : List Val} {rest : List Admin} {dst : Config H} :
    Step P SingleThreaded.Det.noHost ⟨s, f, [.label n [] (vals stack ++ .plain (.br depth) :: rest)]⟩ dst ↔
      (∃ extra payload, stack = extra ++ payload ∧ payload.length = n ∧ depth.toNat = 0 ∧
        dst = ⟨s, f, vals payload⟩) ∨
      (0 < depth.toNat ∧ dst = ⟨s, f, vals stack ++ [.plain (.br (labelPred depth))]⟩) := by
  simpa only [expression, List.map_nil, List.append_nil] using
    (core_label_br_cont_iff (cont := []) (s := s) (f := f) (dst := dst))

theorem core_readback {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {ty : Option NumType} {a : State} {b : Config H}
    (guard : Admitted ty a) (step : Step P host (coreConfig s f ty a) b) :
    ∃ out, Edge ty a out ∧ b = coreConfig s f ty out := by
  cases a with
  | done payload => exact (Step.not_vals step).elim
  | outer below payload =>
    rcases Step.label_inv step with ⟨_, _, _, step, _⟩ | ⟨_, exit, rfl⟩
    · exact (Step.br_vals_stuck step).elim
    rcases label_br_readback (cont := []) exit with ⟨extra, keep, items, len, _, rfl⟩ | ⟨pos, _⟩
    · have typed : payload.map Execution.Runtime.Value.type = ty.toList := guard
      have split : stack below ++ stack payload = extra ++ keep := by
        simpa only [List.map_append] using items
      have sizes := congrArg List.length split
      simp only [List.length_append, len, arity typed] at sizes
      have eq := List.append_inj_right split (Nat.add_right_cancel sizes)
      exact ⟨.done payload, fact (.finish below payload typed), by rw [← eq]; simp [coreConfig, coreCode, expression]⟩
    · exact (Nat.lt_irrefl 0 pos).elim
  | nested n below payload =>
    rcases Step.label_inv step with ⟨_, _, _, inner, rfl⟩ | ⟨_, exit, _⟩
    · rcases Step.label_inv inner with ⟨_, _, _, branch, _⟩ | ⟨_, exit, eq⟩
      · exact (Step.br_vals_stuck branch).elim
      rcases label_br_readback (cont := []) exit with ⟨_, _, _, _, bad, _⟩ | ⟨_, rfl⟩
      · contradiction
      · cases eq
        exact ⟨.outer below payload, fact (.cross n below payload), rfl⟩
    · exact (nested_cannot_exit exit).elim

end Silmaril.Wasm.Institution.Operational.BranchExit.Proofs
