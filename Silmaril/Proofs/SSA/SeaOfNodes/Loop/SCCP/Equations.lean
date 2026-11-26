module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Dataflow.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Defs
public import Silmaril.Semantics.Dataflow.Flat.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Bank

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Proofs

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact TupleLE evalFacts_mono readLocal_mono readWires_mono)
open RVSDG (Tuple)
open Semantics.Dataflow (Flat)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op}

private theorem append_mono {args ports : List (Ty Data)} (input : Tuple (Fact m.value) args)
    {a b : Tuple (Fact m.value) ports} (le : TupleLE a b) :
    TupleLE (appendTuple a input) (appendTuple b input) := by
  induction input with
  | nil => exact le
  | cons _ _ ih =>
    intro t p
    cases p with
    | head => exact le_rfl
    | tail p => exact ih p

private theorem header_mono (g : Graph Op inputs carried entrySigs headerSigs out)
    (input : Tuple (Fact m.value) (dataPorts inputs)) {a b : BankFacts m.value (dataPorts carried)} (le : a ≤ b) :
    let lhs := headerFacts m g input a
    let rhs := headerFacts m g input b
    lhs.guard ≤ rhs.guard ∧ lhs.feedback ≤ rhs.feedback ∧ lhs.result ≤ rhs.result := by
  have hargs := (append_mono input (bankTuple_mono le) : TupleLE _ _)
  have hlocals := evalFacts_mono g.header hargs (lhs := PUnit.unit) (rhs := PUnit.unit) (fun i => i.elim0)
  exact ⟨readLocal_mono g.predicate hargs hlocals,
    tupleFacts_mono (readWires_mono (g.phiInputs .backedge) hargs hlocals),
    readLocal_mono g.result hargs hlocals⟩

private theorem successors_mono : Monotone (successors.{w}) := by
  intro a b le
  change Flat.le a b at le
  cases a <;> cases b <;> simp_all [Flat.le, successors]
  split <;> simp

private theorem control_mono {a b : Executable} {guardA guardB : Flat (ULift.{w} Bool)}
    (edges : a ⊆ b) (guard : guardA ≤ guardB) : control a guardA ⊆ control b guardB := by
  unfold control
  apply Finset.insert_subset_insert
  by_cases marked : incomingIndex .entry ∈ a
  · have marked' := edges marked
    simpa [marked, marked'] using successors_mono guard
  · simp [marked]

private theorem gate_mono {α : Type*} {a b : Executable} (edges : a ⊆ b) (i : Fin 3)
    {v w : Flat α} (values : v ≤ w) : gate a i v ≤ gate b i w := by
  by_cases marked : i ∈ a
  · simpa [gate, marked, show i ∈ b from edges marked] using values
  · simp [gate, marked]

theorem column_le_phiFact {α : Type*} [DecidableEq α] {edges : Executable}
    (entry feedback : Flat α) (edge : Incoming) (marked : incomingIndex edge ∈ edges) :
    edge.select entry feedback ≤ phiFact edges entry feedback := by
  cases edge with
  | entry => simpa [phiFact, gate, marked, Incoming.select] using
      Flat.le_join_left (gate edges (incomingIndex .entry) entry) (gate edges (incomingIndex .backedge) feedback)
  | backedge => simpa [phiFact, gate, marked, Incoming.select] using
      Flat.le_join_right (gate edges (incomingIndex .entry) entry) (gate edges (incomingIndex .backedge) feedback)

theorem phiFact_le_iff {α : Type*} [DecidableEq α] (edges : Executable) (entry feedback upper : Flat α) :
    phiFact edges entry feedback ≤ upper ↔
      ∀ edge, incomingIndex edge ∈ edges → edge.select entry feedback ≤ upper := by
  refine ⟨fun h edge marked => (column_le_phiFact entry feedback edge marked).trans h, ?_⟩
  intro h
  apply Flat.join_le
  · by_cases marked : incomingIndex .entry ∈ edges
    · simpa [gate, marked, Incoming.select] using h .entry marked
    · simp [gate, marked]
  · by_cases marked : incomingIndex .backedge ∈ edges
    · simpa [gate, marked, Incoming.select] using h .backedge marked
    · simp [gate, marked]

variable {value : Data → Type w} {ports : List (Ty Data)}

theorem column_le_phiFacts [equal : BankDecidableEq value ports]
    {edges : Executable} (entry feedback : BankFacts value ports) (edge : Incoming)
    (marked : incomingIndex edge ∈ edges) :
    edge.select entry feedback ≤ phiFacts edges entry feedback := by
  intro i
  have bound := @column_le_phiFact _ (equal.atPort i) edges (entry i) (feedback i) edge marked
  cases edge <;> exact bound

theorem phiFacts_le_iff [equal : BankDecidableEq value ports]
    (edges : Executable) (entry feedback upper : BankFacts value ports) :
    phiFacts edges entry feedback ≤ upper ↔
      ∀ edge, incomingIndex edge ∈ edges → edge.select entry feedback ≤ upper := by
  refine ⟨fun h edge marked => (column_le_phiFacts entry feedback edge marked).trans h, ?_⟩
  intro h i
  apply (@phiFact_le_iff _ (equal.atPort i) edges (entry i) (feedback i) (upper i)).mpr
  intro edge marked
  cases edge <;> exact h _ marked i

theorem transfer_mono [equal : BankDecidableEq m.value (dataPorts carried)]
    (g : Graph Op inputs carried entrySigs headerSigs out)
    (input : Tuple (Fact m.value) (dataPorts inputs)) : Monotone (transfer m g input) := by
  intro a b le
  have h := header_mono g input le.2.1
  refine ⟨control_mono le.1 h.1, ?_, gate_mono le.1 _ h.2.2⟩
  intro i
  let _ := equal.atPort i
  exact Flat.join_le ((gate_mono le.1 _ le_rfl).trans (Flat.le_join_left _ _))
    ((gate_mono le.1 _ (h.2.1 i)).trans (Flat.le_join_right _ _))

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Proofs
