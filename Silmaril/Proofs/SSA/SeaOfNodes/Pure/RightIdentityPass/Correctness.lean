module

public import Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Pass.Thms
import Silmaril.SSA.SeaOfNodes.Pure.SubZero.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass
open Silmaril.SSA.SeaOfNodes.Pure.SubZero
open Diamond (Val ValueSort dataPorts)
open GVN (Producer)
open GVN.Elimination (inFinal)
open Silmaril.SSA.RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program next : Program SubZero.Opcode inputs out}

private theorem mem_wordProducers (ref : Producer program.dataflow word) :
    ref ∈ wordProducers program.dataflow :=
  List.mem_filterMap.mpr ⟨⟨word, ref⟩, GVN.Pass.mem_candidates ref, rfl⟩

private theorem mem_opcodes (opcode : BinaryOpcode) : opcode ∈ opcodes := by
  cases opcode <;> simp [opcodes]

private theorem rewriteCandidate_none_iff (sources : List (Producer program.dataflow word))
    (candidate : Producer program.dataflow word) (opcode : BinaryOpcode) :
    rewriteCandidate? program sources candidate opcode = none ↔
      ∀ source ∈ sources, rewriteRightIdentity? opcode program candidate source = none := by
  cases operands : operandsFor? opcode candidate with
  | none => simp [rewriteCandidate?, rewriteRightIdentity?, operands]
  | some pair =>
    obtain ⟨lhs, rhs⟩ := pair
    simp only [rewriteCandidate?, operands, Option.bind_some, List.findSome?_eq_none_iff]
    constructor
    · intro miss source listed
      by_cases same : (inFinal candidate rhs).address = source.origin.address
      · simpa only [ite_eq_left same] using miss source listed
      · simp [rewriteRightIdentity?, operands, same]
    · intro miss source listed
      rw [miss source listed]
      split <;> rfl

theorem step_none_iff (program : Program SubZero.Opcode inputs out) :
    step? program = none ↔ Normal program := by
  simp only [step?, List.findSome?_eq_none_iff, rewriteCandidate_none_iff]
  constructor
  · intro miss opcode candidate source
    exact miss candidate (mem_wordProducers candidate) opcode (mem_opcodes opcode)
      source (mem_wordProducers source)
  · intro normal candidate _ opcode _ source _
    exact normal opcode candidate source

theorem step_checked (accepted : step? program = some next) :
    ∃ (opcode : BinaryOpcode) (candidate source : Producer program.dataflow word),
      rewriteRightIdentity? opcode program candidate source = some next := by
  obtain ⟨candidate, _, found⟩ := List.exists_of_findSome?_eq_some accepted
  obtain ⟨opcode, _, checked⟩ := List.exists_of_findSome?_eq_some found
  cases operands : operandsFor? opcode candidate with
  | none => simp [rewriteCandidate?, operands] at checked
  | some pair =>
    obtain ⟨lhs, rhs⟩ := pair
    simp only [rewriteCandidate?, operands, Option.bind_some] at checked
    obtain ⟨source, _, checked⟩ := List.exists_of_findSome?_eq_some checked
    split at checked
    · exact ⟨opcode, candidate, source, checked⟩
    · cases checked

theorem step_size (accepted : step? program = some next) :
    next.sigs.length + 1 = program.sigs.length := by
  obtain ⟨_, _, _, checked⟩ := step_checked accepted
  exact rightIdentity_count checked

theorem step_eval_eq (accepted : step? program = some next)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    next.eval model entry = program.eval model entry := by
  obtain ⟨_, _, _, checked⟩ := step_checked accepted
  exact rightIdentity_eval_eq checked entry

theorem run_eval_eq (fuel : Nat) (program : Program SubZero.Opcode inputs out)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (run fuel program).program.eval model entry = program.eval model entry := by
  induction fuel generalizing program with
  | zero => rfl
  | succ fuel ih =>
    cases found : step? program with
    | none => simp only [run, found]
    | some next =>
      simp only [run, found]
      exact (ih next).trans (step_eval_eq found entry)

theorem run_progress (fuel : Nat) (program : Program SubZero.Opcode inputs out) :
    let final := run fuel program
    final.program.sigs.length + final.deletions = program.sigs.length ∧ final.deletions ≤ fuel := by
  induction fuel generalizing program with
  | zero => simp [run]
  | succ fuel ih =>
    cases found : step? program with
    | none => simp [run, found]
    | some next =>
      obtain ⟨size, budget⟩ := ih next
      have stepSize := step_size found
      simp only [run, found]
      omega

theorem run_normal_of_remaining (fuel : Nat) (program : Program SubZero.Opcode inputs out)
    (remaining : (run fuel program).deletions < fuel) : Normal (run fuel program).program := by
  induction fuel generalizing program with
  | zero => exact False.elim (Nat.not_lt_zero _ remaining)
  | succ fuel ih =>
    cases found : step? program with
    | none =>
      simp only [run, found]
      exact (step_none_iff program).1 found
    | some next =>
      simp only [run, found] at remaining ⊢
      exact ih next (Nat.lt_of_succ_lt_succ remaining)

theorem normalize_normal (program : Program SubZero.Opcode inputs out) : Normal (normalize program).program := by
  have counted := (run_progress (program.sigs.length + 1) program).1
  exact run_normal_of_remaining (program.sigs.length + 1) program (by omega)

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass
