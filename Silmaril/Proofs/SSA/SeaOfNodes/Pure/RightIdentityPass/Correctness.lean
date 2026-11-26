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

section Driver

variable (advance : Program SubZero.Opcode inputs out → Option (Program SubZero.Opcode inputs out))

theorem runWith_eval_eq (fuel : Nat) (program : Program SubZero.Opcode inputs out)
    (preserves : ∀ {current next}, advance current = some next →
      ∀ (entry : Tuple (Val model.value) (dataPorts inputs)),
        next.eval model entry = current.eval model entry)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (runWith advance fuel program).program.eval model entry = program.eval model entry := by
  induction fuel generalizing program with
  | zero => rfl
  | succ fuel ih =>
    cases found : advance program with
    | none => simp only [runWith, found]
    | some next =>
      simp only [runWith, found]
      exact (ih next).trans (preserves found entry)

theorem runWith_progress (fuel : Nat) (program : Program SubZero.Opcode inputs out)
    (shrinks : ∀ {current next}, advance current = some next →
      next.sigs.length + 1 = current.sigs.length) :
    let final := runWith advance fuel program
    final.program.sigs.length + final.deletions = program.sigs.length ∧ final.deletions ≤ fuel := by
  induction fuel generalizing program with
  | zero => simp [runWith]
  | succ fuel ih =>
    cases found : advance program with
    | none => simp [runWith, found]
    | some next =>
      obtain ⟨size, budget⟩ := ih next
      have stepSize := shrinks found
      simp only [runWith, found]
      omega

theorem runWith_stopped_of_remaining (fuel : Nat) (program : Program SubZero.Opcode inputs out)
    (remaining : (runWith advance fuel program).deletions < fuel) :
    advance (runWith advance fuel program).program = none := by
  induction fuel generalizing program with
  | zero => exact False.elim (Nat.not_lt_zero _ remaining)
  | succ fuel ih =>
    cases found : advance program with
    | none => simp only [runWith, found]
    | some next =>
      simp only [runWith, found] at remaining ⊢
      exact ih next (Nat.lt_of_succ_lt_succ remaining)

theorem runWith_stopped (fuel : Nat) (program : Program SubZero.Opcode inputs out)
    (shrinks : ∀ {current next}, advance current = some next →
      next.sigs.length + 1 = current.sigs.length) (enough : program.sigs.length ≤ fuel) :
    advance (runWith advance fuel program).program = none := by
  by_cases remaining : (runWith advance fuel program).deletions < fuel
  · exact runWith_stopped_of_remaining advance fuel program remaining
  cases found : advance (runWith advance fuel program).program with
  | none => rfl
  | some next =>
    have ⟨count, _⟩ := runWith_progress advance fuel program shrinks
    have decreased := shrinks found
    omega

end Driver

theorem run_eval_eq (fuel : Nat) (program : Program SubZero.Opcode inputs out)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (run fuel program).program.eval model entry = program.eval model entry :=
  runWith_eval_eq step? fuel program (fun h => step_eval_eq h) entry

theorem run_progress (fuel : Nat) (program : Program SubZero.Opcode inputs out) :
    let final := run fuel program
    final.program.sigs.length + final.deletions = program.sigs.length ∧ final.deletions ≤ fuel :=
  runWith_progress step? fuel program (fun h => step_size h)

theorem run_normal_of_remaining (fuel : Nat) (program : Program SubZero.Opcode inputs out)
    (remaining : (run fuel program).deletions < fuel) : Normal (run fuel program).program :=
  (step_none_iff _).1 (runWith_stopped_of_remaining step? fuel program remaining)

theorem normalize_normal (program : Program SubZero.Opcode inputs out) : Normal (normalize program).program := by
  exact (step_none_iff _).1 (runWith_stopped step? _ program (fun h => step_size h) (Nat.le_succ _))

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass
