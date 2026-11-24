module
public import Silmaril.Formats.Sqlite.Vdbe.Defs

@[expose] public section
namespace Silmaril.Formats.Sqlite.Vdbe

theorem execute_complete {database instruction before after}
    (transition : InstructionStep database instruction before after) :
    execute database instruction before = .ok after := by
  cases transition <;> simp_all [execute]

theorem InstructionStep.of_ok_eq {database instruction before expected after}
    (transition : InstructionStep database instruction before expected)
    (equality : (Except.ok expected : Except Error State) = .ok after) :
    InstructionStep database instruction before after :=
  Except.ok.inj equality ▸ transition

theorem execute_no_error {database instruction before after} (error : Error)
    (success : execute database instruction before = .ok after)
    (failure : execute database instruction before = .error error) : False := by
  have impossible : (Except.error error : Except Error State) = .ok after := failure.symm.trans success
  cases impossible

theorem execute_sound (database : Database) (instruction : Instruction) (before after : State)
    (success : execute database instruction before = .ok after) :
    InstructionStep database instruction before after := by
  cases instruction with
  | init target => exact (InstructionStep.init before target).of_ok_eq success
  | goto target => exact (InstructionStep.goto before target).of_ok_eq success
  | halt code => exact (InstructionStep.halt before code).of_ok_eq success
  | integer value destination => exact (InstructionStep.integer before value destination).of_ok_eq success
  | int64 value destination => exact (InstructionStep.int64 before value destination).of_ok_eq success
  | string8 value destination => exact (InstructionStep.string8 before value destination).of_ok_eq success
  | null first last => exact (InstructionStep.null before first last).of_ok_eq success
  | copy source destination additional => exact (InstructionStep.copy before source destination additional).of_ok_eq success
  | openRead identifier root databaseId =>
      show InstructionStep database (.openRead identifier root databaseId) before after
      cases found : database databaseId root with
      | none => exact False.elim (execute_no_error (.missingTable databaseId root) success (by simp [execute, found]))
      | some table =>
          have equality : (Except.ok ((before.setCursor identifier {table := table}).advance) :
              Except Error State) = .ok after := by simpa only [execute, found] using success
          exact (InstructionStep.openRead found).of_ok_eq equality
  | rewind identifier target =>
      show InstructionStep database (.rewind identifier target) before after
      cases found : before.cursors identifier with
      | none => exact False.elim (execute_no_error (.missingCursor identifier) success (by simp [execute, found]))
      | some cursor =>
          show InstructionStep database (.rewind identifier target) before after
          by_cases invalid : cursor.table.entries.isEmpty = true ∧ target = 0
          · exact False.elim (execute_no_error .emptyRewindAssertion success (by simp [execute, found, invalid]))
          · have equality : (Except.ok (before.rewindCursor identifier target cursor) :
                Except Error State) = .ok after := by
              simpa only [execute, found, ite_eq_right invalid] using success
            exact (InstructionStep.rewind found invalid).of_ok_eq equality
  | next identifier target =>
      show InstructionStep database (.next identifier target) before after
      cases found : before.cursors identifier with
      | none => exact False.elim (execute_no_error (.missingCursor identifier) success (by simp [execute, found]))
      | some cursor =>
          show InstructionStep database (.next identifier target) before after
          by_cases invalid : cursor.forward = false
          · exact False.elim (execute_no_error .invalidAdvance success (by simp [execute, found, invalid]))
          · cases positioned : cursor.remaining with
            | none => exact False.elim (execute_no_error (.unpositionedCursor identifier) success (by simp [execute, found, invalid, positioned]))
            | some remaining =>
                have equality : (Except.ok (before.nextCursor identifier target cursor remaining) :
                    Except Error State) = .ok after := by
                  simpa only [execute, found, ite_eq_right invalid, positioned] using success
                exact (InstructionStep.next found invalid positioned).of_ok_eq equality
  | column identifier column destination =>
      show InstructionStep database (.column identifier column destination) before after
      cases found : before.cursors identifier with
      | none => exact False.elim (execute_no_error (.missingCursor identifier) success (by simp [execute, found]))
      | some cursor =>
          show InstructionStep database (.column identifier column destination) before after
          cases current : cursor.current? with
          | none => exact False.elim (execute_no_error (.noCurrentRow identifier) success (by simp [execute, found, current]))
          | some entry =>
              have equality : (Except.ok ((before.write destination (entry.2[column]?.getD .null)).advance) :
                  Except Error State) = .ok after := by simpa only [execute, found, current] using success
              exact (InstructionStep.column found current).of_ok_eq equality
  | rowid identifier destination =>
      show InstructionStep database (.rowid identifier destination) before after
      cases found : before.cursors identifier with
      | none => exact False.elim (execute_no_error (.missingCursor identifier) success (by simp [execute, found]))
      | some cursor =>
          show InstructionStep database (.rowid identifier destination) before after
          cases current : cursor.current? with
          | none => exact False.elim (execute_no_error (.noCurrentRow identifier) success (by simp [execute, found, current]))
          | some entry =>
              show InstructionStep database (.rowid identifier destination) before after
              by_cases range : -(2^63 : Int) ≤ entry.1 ∧ entry.1 < 2^63
              · have equality : (Except.ok ((before.write destination (.integer (Int64.ofInt entry.1))).advance) :
                    Except Error State) = .ok after := by
                  simpa only [execute, found, current, ite_eq_left range] using success
                exact (InstructionStep.rowid found current range).of_ok_eq equality
              · have impossible : (Except.error (.rowidRange entry.1) : Except Error State) = .ok after := by
                  simpa only [execute, found, current, ite_eq_right range] using success
                cases impossible
  | resultRow first count => exact (InstructionStep.resultRow before first count).of_ok_eq success
  | seekRowid identifier target register =>
      show InstructionStep database (.seekRowid identifier target register) before after
      cases found : before.cursors identifier with
      | none => exact False.elim (execute_no_error (.missingCursor identifier) success (by simp [execute, found]))
      | some cursor =>
          show InstructionStep database (.seekRowid identifier target register) before after
          cases integer : before.registers register with
          | null => exact False.elim (execute_no_error .unsupportedSeekKey success (by simp [execute, found, integer]))
          | real bits => exact False.elim (execute_no_error .unsupportedSeekKey success (by simp [execute, found, integer]))
          | text value => exact False.elim (execute_no_error .unsupportedSeekKey success (by simp [execute, found, integer]))
          | blob value => exact False.elim (execute_no_error .unsupportedSeekKey success (by simp [execute, found, integer]))
          | integer key =>
              show InstructionStep database (.seekRowid identifier target register) before after
              by_cases invalid : (cursor.table.entries.dropWhile (fun entry => entry.1 != key.toInt)).isEmpty = true ∧ target = 0
              · exact False.elim (execute_no_error .missingSeekAssertion success (by simp [execute, found, integer, invalid]))
              · have equality : (Except.ok (before.seekCursor identifier target cursor key) :
                    Except Error State) = .ok after := by
                  simpa only [execute, found, integer, ite_eq_right invalid] using success
                exact (InstructionStep.seekRowid found integer invalid).of_ok_eq equality

theorem execute_iff_proof {database instruction before after} :
    execute database instruction before = .ok after ↔
      InstructionStep database instruction before after :=
  ⟨execute_sound database instruction before after, execute_complete⟩

theorem step_sound (database : Database) (program : Program) (before after : State)
    (success : step database program before = .ok after) : Step database program before after := by
  cases active : before.halted with
  | some code => simp [step, active] at success
  | none =>
      cases fetch : program[before.pc]? with
      | none => simp [step, active, fetch] at success
      | some instruction =>
          have executed : execute database instruction before = .ok after := by
            simpa [step, active, fetch] using success
          exact .instruction active fetch (execute_sound database instruction before after executed)

theorem step_complete {database program before after}
    (transition : Step database program before after) : step database program before = .ok after := by
  cases transition with
  | instruction active fetch transition =>
      simp [step, active, fetch, execute_complete transition]

theorem step_iff_proof {database program before after} :
    step database program before = .ok after ↔ Step database program before after :=
  ⟨step_sound database program before after, step_complete⟩

theorem Step.deterministic {database program before left right}
    (first : Step database program before left) (second : Step database program before right) :
    left = right := by
  have equal : (Except.ok left : Except Error State) = .ok right :=
    (step_complete first).symm.trans (step_complete second)
  exact Except.ok.inj equal

theorem Trace.trans {database program before middle after}
    (first : Trace database program before middle) (second : Trace database program middle after) :
    Trace database program before after := by
  induction first with
  | refl => exact second
  | cons step _ inductionHypothesis => exact .cons step (inductionHypothesis second)

/-- Every returned state has a finite derivation from the input, including
fuel exhaustion and errors. No successful instruction is hidden in a fault. -/
theorem run_trace_proof (database : Database) (program : Program) (fuel : Nat) (before : State) :
    Trace database program before (run database program fuel before).state := by
  induction fuel generalizing before with
  | zero =>
      cases active : before.halted with
      | none => simp [run, active, RunResult.state, Trace.refl]
      | some code => simp [run, active, RunResult.state, Trace.refl]
  | succ fuel inductionHypothesis =>
      cases active : before.halted with
      | some code => simp [run, active, RunResult.state, Trace.refl]
      | none =>
          cases success : step database program before with
          | error error => simp [run, active, success, RunResult.state, Trace.refl]
          | ok middle =>
              have first : Step database program before middle :=
                step_sound database program before middle success
              simpa [run, active, success] using
                Trace.cons first (inductionHypothesis middle)

end Silmaril.Formats.Sqlite.Vdbe
