module

public import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Defs
public import Silmaril.Wasm.Institution.Operational.BranchExit.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.BranchExit.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame Value AdminInstr)

private def first (code : List Admin) := code.find? (fun a => (asValue? a).isNone)

@[simp] private theorem first_value (v : Value) (tail : List Admin) :
    first (value v :: tail) = first tail := by
  simp [first, asValue?_value]

@[simp] private theorem first_prefix (vs : List Value) (tail : List Admin) :
    first (values vs ++ tail) = first tail := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change first (value v :: (values vs ++ tail)) = first tail
    rw [first_value, ih]

@[simp] private theorem first_values (vs : List Value) : first (values vs) = none := by
  change first (values vs) = first []
  rw [← first_prefix vs [], List.append_nil]

@[simp] private theorem first_head {a : Admin} (tail : List Admin) (ha : asValue? a = none) :
    first (a :: tail) = some a := by
  simp [first, ha]

private theorem first_step {H : Type} {host : HostSemantics H} {a b : Config H}
    (step : Step host a b) : first a.code ≠ none := by
  intro eq
  obtain ⟨op, member, hv⟩ := step.nonvalue
  simpa [hv] using List.find?_eq_none.mp eq op member

private theorem br_stuck {H : Type} {host : HostSemantics H} {a b : Config H}
    (step : Step host a b) {l : LabelIdx}
    (eq : first a.code = some (.source (.br l))) : False := by
  induction step with
  | pure s f h =>
    cases h <;>
      (simp only [List.append_assoc, List.singleton_append, first_prefix, first_value] at eq) <;>
      simp [first, asValue?] at eq
  | @context _ _ _ _ before _ h saved tail ih =>
    change first (values saved ++ before ++ tail) = _ at eq
    rw [List.append_assoc, first_prefix] at eq
    change (List.find? _ (before ++ tail)) = _ at eq
    rw [List.find?_append] at eq
    change (first before).or (first tail) = _ at eq
    cases he : first before with
    | none => exact first_step h he
    | some op =>
      rw [he] at eq
      exact ih (he.trans eq)
  | _ =>
    simp only [first_prefix, first_value] at eq
    simp [first, asValue?] at eq

private inductive LabelStep {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    (n : Nat) (body : List Admin) : Config H → Prop where
  | pure {out} (h : PureStep f.module.types [.label n [] body] out) :
      LabelStep host s f n body ⟨s, f, out⟩
  | inside {target} (h : Step host ⟨s, f, body⟩ target) :
      LabelStep host s f n body ⟨target.store, target.frame, [.label n [] target.code]⟩

private theorem label_inv {H : Type} {host : HostSemantics H} {a b : Config H}
    (step : Step host a b) {n : Nat} {body : List Admin} (eq : a.code = [.label n [] body]) :
    LabelStep host a.store a.frame n body b := by
  induction step with
  | pure s f h => exact .pure (eq ▸ h)
  | label h j cont _ =>
    obtain ⟨rfl, rfl, rfl⟩ := AdminInstr.label.inj (List.cons.inj eq).1
    exact .inside h
  | @context _ _ _ _ before _ h saved tail ih =>
    change values saved ++ before ++ tail = [_] at eq
    have lengths := congrArg List.length eq
    simp only [List.length_append, values_length, List.length_cons, List.length_nil] at lengths
    have pos : 0 < before.length := List.length_pos_iff.mpr (by
      obtain ⟨op, member, _⟩ := h.nonvalue
      exact List.ne_nil_of_mem member)
    have hs : saved = [] := List.eq_nil_of_length_eq_zero (by omega)
    have ht : tail = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst saved tail
    simpa [values] using ih (by simpa [values] using eq)
  | _ =>
    have head := congrArg first eq
    simp only [first_prefix, first_value] at head
    simp [first, asValue?] at head

private theorem split_values (vs : List Value) {a : Admin} (tail : List Admin)
    (ha : asValue? a = none) : splitValues (values vs ++ a :: tail) = (vs, a :: tail) := by
  induction vs with
  | nil =>
    change splitValues (a :: tail) = ([], a :: tail)
    simp [splitValues, ha]
  | cons v vs ih =>
    change splitValues (value v :: (values vs ++ a :: tail)) = _
    simp [splitValues, asValue?_value, ih]

private theorem nested_cannot_exit {types : List Wasm.Lime1.FuncType} {n m : Nat}
    {body out : List Admin} (h : PureStep types [.label n [] [.label m [] body]] out) : False := by
  generalize eq : ([.label n [] [.label m [] body]] : List Admin) = before at h
  have outerHead := congrArg first eq
  cases h <;> first
    | solve
      | simp only [List.cons.injEq, AdminInstr.label.injEq, and_true] at eq
        have head := congrArg first eq.2.2
        simp only [List.append_assoc, List.singleton_append, first_prefix, first_values] at head
        simp [first, asValue?] at head
    | (try simp only [List.append_assoc, List.singleton_append, first_prefix, first_value] at outerHead)
      simp [first, asValue?] at outerHead

private theorem label_br_readback {types : List Wasm.Lime1.FuncType} {n : Nat}
    {l : LabelIdx} {vs : List Value} {out : List Admin}
    (h : PureStep types [.label n [] (values vs ++ [.source (.br l)])] out) :
    (∃ below payload, vs = below ++ payload ∧ payload.length = n ∧ l.toNat = 0 ∧ out = values payload) ∨
      (l.toNat ≠ 0 ∧ out = values vs ++ [.source (.br (lowerLabel l))]) := by
  generalize eq : ([.label n [] (values vs ++ [.source (.br l)])] : List Admin) = before at h
  have outerHead := congrArg first eq
  cases h <;> try simp only [List.cons.injEq, and_true, AdminInstr.label.injEq] at eq
  case labelBranch n' cont extra payload tail len =>
    obtain ⟨rfl, rfl, code⟩ := eq
    rw [List.append_assoc, List.singleton_append, ← values_append] at code
    have decoded := congrArg splitValues code
    rw [split_values vs [] rfl, split_values (extra ++ payload) tail rfl] at decoded
    obtain ⟨stackEq, branchEq⟩ := Prod.mk.inj decoded
    cases (List.cons.inj branchEq).1
    exact .inl ⟨extra, payload, stackEq, len, rfl, by simp [expression]⟩
  case labelBranchOuter n' cont stack tail l' pos =>
    obtain ⟨rfl, rfl, code⟩ := eq
    rw [List.append_assoc, List.singleton_append] at code
    have decoded := congrArg splitValues code
    rw [split_values vs [] rfl, split_values stack tail rfl] at decoded
    obtain ⟨rfl, branchEq⟩ := Prod.mk.inj decoded
    cases (List.cons.inj branchEq).1
    exact .inr ⟨pos, rfl⟩
  all_goals first
    | solve
      | have head := congrArg first eq.2.2
        simp only [List.append_assoc, List.singleton_append, first_prefix, first_values] at head
        simp [first, asValue?] at head
    | (try simp only [List.append_assoc, List.singleton_append, first_prefix, first_value] at outerHead)
      simp [first, asValue?] at outerHead

theorem sound {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {ty : Option NumType} {a b : State} (edge : Edge ty a b) :
    Step host (limeConfig s f ty a) (limeConfig s f ty b) := by
  cases invert edge with
  | cross n below payload =>
    have lowered : lowerLabel (⟨1⟩ : LabelIdx) = ⟨0⟩ := by decide
    simpa only [limeConfig, limeCode, List.append_nil, lowered] using
      (Step.label (Step.pure (host := host) s f (.labelBranchOuter n [] (below ++ payload) [] ⟨1⟩
        (by decide))) ty.toList.length [])
  | finish below payload typed =>
    have arity : payload.length = ty.toList.length := by simpa using congrArg List.length typed
    simpa only [limeConfig, limeCode, values_append, List.append_nil, expression, List.map_nil] using
      (Step.pure (host := host) s f (.labelBranch ty.toList.length [] below payload [] arity))

theorem readback {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {ty : Option NumType} {a : State} {b : Config H}
    (guard : Admitted ty a) (step : Step host (limeConfig s f ty a) b) :
    ∃ out, Edge ty a out ∧ b = limeConfig s f ty out := by
  cases a with
  | done payload =>
    exact (first_step step (first_values payload)).elim
  | outer below payload =>
    cases label_inv step rfl with
    | inside h => exact (br_stuck h (by rw [first_prefix]; rfl)).elim
    | pure h =>
      rcases label_br_readback h with ⟨extra, keep, items, len, _, rfl⟩ | ⟨bad, _⟩
      · have typed : payload.map Value.type = ty.toList := guard
        have plen : payload.length = ty.toList.length := by simpa using congrArg List.length typed
        have sizes := congrArg List.length items
        simp only [List.length_append, len, plen] at sizes
        have eq := List.append_inj_right items (Nat.add_right_cancel sizes)
        exact ⟨.done payload, fact (.finish below payload typed), by rw [← eq]; rfl⟩
      · exact (bad rfl).elim
  | nested n below payload =>
    cases label_inv step rfl with
    | pure h => exact (nested_cannot_exit h).elim
    | inside outerStep =>
      cases label_inv outerStep rfl with
      | inside branchStep => exact (br_stuck branchStep (by rw [first_prefix]; rfl)).elim
      | pure innerExit =>
        rcases label_br_readback innerExit with ⟨_, _, _, _, bad, _⟩ | ⟨_, rfl⟩
        · contradiction
        · exact ⟨.outer below payload, fact (.cross n below payload), rfl⟩

end Silmaril.Wasm.Institution.Operational.BranchExit.Proofs.Lime1
