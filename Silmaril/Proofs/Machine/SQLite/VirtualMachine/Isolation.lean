module

public import Silmaril.Machine.SQLite.VirtualMachine.Isolation.Defs

public section

namespace Silmaril.Proofs.Machine.SQLite.VirtualMachine.Isolation

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite.VirtualMachine
open Silmaril.Machine.SQLite.VirtualMachine.Isolation

theorem effect_isAllowed_iff (policy : Policy) (e : Effect) :
    e.isAllowed policy = true ↔ e.Allowed policy := by
  cases e <;> simp [Effect.isAllowed, Effect.Allowed]

theorem checkInstruction_ok_iff (policy : Policy) (codeSize : Nat) (instr : Instruction) :
    checkInstruction policy codeSize instr = .ok () ↔ InstructionWf policy codeSize instr := by
  cases instr with
  | init target =>
      simp only [checkInstruction, InstructionWf]
      by_cases h : target = 0 ∨ target < codeSize <;> simp [h]
  | goto target =>
      simp [checkInstruction, InstructionWf]
  | halt code =>
      simp [checkInstruction, InstructionWf]
  | integer value destination =>
      simp [checkInstruction, InstructionWf]
  | int64 value destination =>
      simp [checkInstruction, InstructionWf]
  | string8 value destination =>
      simp [checkInstruction, InstructionWf]
  | null first last =>
      simp only [checkInstruction, InstructionWf]
      by_cases h : 1 ≤ first ∧ max first last ≤ policy.maxRegisters <;> simp [h]
  | copy source destination additional =>
      by_cases h1 : 1 ≤ source ∧ source + additional ≤ policy.maxRegisters <;>
      by_cases h2 : 1 ≤ destination ∧ destination + additional ≤ policy.maxRegisters <;>
      simp [checkInstruction, InstructionWf, h1, h2]
  | openRead cursor root database =>
      cases hdb : policy.canRead database root <;>
      by_cases hc : cursor < policy.maxCursors <;>
      simp [checkInstruction, InstructionWf, hdb, hc]
  | rewind cursor emptyTarget =>
      by_cases hc : cursor < policy.maxCursors <;>
      by_cases ht : emptyTarget = 0 ∨ emptyTarget < codeSize <;>
      simp [checkInstruction, InstructionWf, hc, ht]
  | next cursor loopTarget =>
      by_cases hc : cursor < policy.maxCursors <;>
      by_cases ht : loopTarget < codeSize <;>
      simp [checkInstruction, InstructionWf, hc, ht]
  | column cursor col destination =>
      by_cases hc : cursor < policy.maxCursors <;>
      by_cases hr : 1 ≤ destination ∧ destination ≤ policy.maxRegisters <;>
      simp [checkInstruction, InstructionWf, hc, hr]
  | rowid cursor destination =>
      by_cases hc : cursor < policy.maxCursors <;>
      by_cases hr : 1 ≤ destination ∧ destination ≤ policy.maxRegisters <;>
      simp [checkInstruction, InstructionWf, hc, hr]
  | resultRow first count =>
      simp only [checkInstruction, InstructionWf]
      split
      · rename_i hw
        have hnw : ¬ count ≤ policy.maxResultWidth := by simpa using hw
        exact ⟨fun h => (by cases h), fun h => False.elim (hnw h.1)⟩
      · rename_i hw
        have hcw : count ≤ policy.maxResultWidth := by simpa using hw
        split
        · rename_i hr
          have hnr : ¬ (count = 0 ∨ 1 ≤ first ∧ first + count - 1 ≤ policy.maxRegisters) := by
            intro h; simp at hr; omega
          exact ⟨fun h => (by cases h), fun h => False.elim (hnr h.2)⟩
        · rename_i hr
          have hcr : count = 0 ∨ 1 ≤ first ∧ first + count - 1 ≤ policy.maxRegisters := by
            have h : ¬count = 0 → ¬first = 0 ∧ first + count ≤ policy.maxRegisters + 1 := by
              simpa using hr
            by_cases h0 : count = 0
            · exact Or.inl h0
            · obtain ⟨h1, h2⟩ := h h0
              exact Or.inr ⟨by omega, by omega⟩
          exact ⟨fun _ => ⟨hcw, hcr⟩, fun _ => rfl⟩
  | seekRowid cursor missingTarget keyRegister =>
      by_cases hc : cursor < policy.maxCursors <;>
      by_cases ht : missingTarget = 0 ∨ missingTarget < codeSize <;>
      by_cases hr : 1 ≤ keyRegister ∧ keyRegister ≤ policy.maxRegisters <;>
      simp [checkInstruction, InstructionWf, hc, ht, hr]

theorem admitInstruction_wf {policy : Policy} {codeSize : Nat} {raw : RawInstruction}
    {instr : Instruction} (h : admitInstruction policy codeSize raw = .ok instr) :
    InstructionWf policy codeSize instr := by
  unfold admitInstruction at h
  cases hname : raw.opcode.name? with
  | none =>
      simp [hname] at h
  | some name =>
      simp only [hname] at h
      by_cases hden : name ∈ deniedOpcodeNames
      · simp [hden] at h
      · simp only [hden, ↓reduceIte] at h
        cases hdec : Vdbe.decode? raw with
        | none =>
            simp [hdec] at h
        | some decoded =>
            simp only [hdec] at h
            cases hchk : checkInstruction policy codeSize decoded with
            | error e =>
                simp [hchk, bind, Except.bind] at h
            | ok u =>
                cases u
                simp only [hchk, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
                subst h
                exact (checkInstruction_ok_iff policy codeSize decoded).mp hchk

private theorem list_mapM_except_ok {α β ε : Type} (f : α → Except ε β) :
    ∀ (xs : List α) (ys : List β),
      xs.mapM f = .ok ys →
      ys.length = xs.length ∧ ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, by intro y hy; cases hy⟩
  | x :: xs, ys, h => by
      simp only [List.mapM_cons, bind, Except.bind] at h
      cases hfx : f x with
      | error e =>
          simp [hfx] at h
      | ok y =>
          simp only [hfx] at h
          cases hrest : xs.mapM f with
          | error e =>
              simp [hrest] at h
          | ok rest =>
              simp only [hrest, pure, Except.pure, Except.ok.injEq] at h
              subst h
              have ih := list_mapM_except_ok f xs rest hrest
              refine ⟨by simp [ih.1], ?_⟩
              intro z hz
              rcases List.mem_cons.mp hz with rfl | hz'
              · exact ⟨x, List.mem_cons_self, hfx⟩
              · obtain ⟨x', hx', hfx'⟩ := ih.2 z hz'
                exact ⟨x', List.mem_cons_of_mem x hx', hfx'⟩

theorem admitProgram_wellFormed {policy : Policy} {raw : Vdbe.RawProgram} {program : Program}
    (h : admitProgram policy raw = .ok program) :
    WellFormed policy program := by
  unfold admitProgram at h
  cases hlist : raw.toList.mapM (admitInstruction policy raw.size) with
  | error e =>
      simp [hlist, Except.map] at h
  | ok xs =>
      simp only [hlist, Except.map, Except.ok.injEq] at h
      subst h
      obtain ⟨hlen, hall⟩ := list_mapM_except_ok (admitInstruction policy raw.size) raw.toList xs hlist
      have hsize : xs.toArray.size = raw.size := by
        simpa [Array.length_toList] using hlen
      intro i instr hget
      have hmem : instr ∈ xs := by
        rcases (Array.getElem?_eq_some_iff.mp hget) with ⟨hi, rfl⟩
        simp
      obtain ⟨r, _, hr⟩ := hall instr hmem
      rw [hsize]
      exact admitInstruction_wf hr

theorem stateInv_initial (policy : Policy) (host : HostState) :
    StateInv policy host initial where
  registersConfined := fun _ h => False.elim (h rfl)
  cursorsConfined := fun _ _ h => by cases h
  rowsBounded := fun _ h => by cases h

private theorem stateInv_advance {policy : Policy} {host : HostState} {s : State}
    (hinv : StateInv policy host s) :
    StateInv policy host s.advance :=
  ⟨hinv.registersConfined, hinv.cursorsConfined, hinv.rowsBounded⟩

private theorem stateInv_jump {policy : Policy} {host : HostState} {s : State} {target : Nat}
    (hinv : StateInv policy host s) :
    StateInv policy host (s.jump target) :=
  ⟨hinv.registersConfined, hinv.cursorsConfined, hinv.rowsBounded⟩

private theorem stateInv_write {policy : Policy} {host : HostState} {s : State}
    {dest : Nat} {val : Value}
    (hinv : StateInv policy host s)
    (hdest : 1 ≤ dest ∧ dest ≤ policy.maxRegisters) :
    StateInv policy host (s.write dest val) where
  registersConfined := by
    intro r hr
    by_cases heq : r = dest
    · subst heq; exact hdest
    · apply hinv.registersConfined r
      simpa [Vdbe.State.write, heq] using hr
  cursorsConfined := hinv.cursorsConfined
  rowsBounded := hinv.rowsBounded

private theorem stateInv_writeNull {policy : Policy} {host : HostState} {s : State}
    {first last : Nat} (hinv : StateInv policy host s) :
    StateInv policy host (s.writeNull first last) where
  registersConfined := by
    intro r hr
    by_cases hin : first ≤ r ∧ r ≤ max first last
    · exfalso
      simp only [Vdbe.State.writeNull, ite_eq_left hin] at hr
      exact hr rfl
    · apply hinv.registersConfined r
      simpa only [Vdbe.State.writeNull, ite_eq_right hin] using hr
  cursorsConfined := hinv.cursorsConfined
  rowsBounded := hinv.rowsBounded

private theorem stateInv_copyRegisters {policy : Policy} {host : HostState} :
    ∀ (count src dst : Nat) (s : State),
      StateInv policy host s →
      (count = 0 ∨ (1 ≤ dst ∧ dst + count - 1 ≤ policy.maxRegisters)) →
      StateInv policy host (Vdbe.State.copyRegisters count src dst s)
  | 0, _, _, s, hinv, _ => hinv
  | count + 1, src, dst, s, hinv, hbounds => by
      have hdst : 1 ≤ dst ∧ dst ≤ policy.maxRegisters := by
        rcases hbounds with h0 | ⟨h1, h2⟩
        · cases h0
        · exact ⟨h1, by omega⟩
      have hnext : count = 0 ∨ (1 ≤ dst + 1 ∧ (dst + 1) + count - 1 ≤ policy.maxRegisters) := by
        cases count with
        | zero => exact Or.inl rfl
        | succ k =>
            rcases hbounds with h0 | ⟨h1, h2⟩
            · cases h0
            · exact Or.inr ⟨by omega, by omega⟩
      exact stateInv_copyRegisters count (src + 1) (dst + 1)
        (s.write dst (s.registers src))
        (stateInv_write hinv hdst)
        hnext

private theorem stateInv_setCursor_authorized {policy : Policy} {host : HostState} {s : State}
    {cid db root : Nat} {cursor : Vdbe.Cursor}
    (hinv : StateInv policy host s)
    (hcid : cid < policy.maxCursors)
    (hauth : policy.canRead db root = true)
    (hfound : host.databases db root = some cursor.table) :
    StateInv policy host (s.setCursor cid cursor) where
  registersConfined := hinv.registersConfined
  cursorsConfined := by
    intro id c hc
    by_cases heq : id = cid
    · subst heq
      simp only [Vdbe.State.setCursor, ↓reduceIte, Option.some.injEq] at hc
      subst hc
      exact ⟨hcid, db, root, hauth, hfound⟩
    · apply hinv.cursorsConfined id c
      simpa [Vdbe.State.setCursor, heq] using hc
  rowsBounded := hinv.rowsBounded

private theorem stateInv_updateCursor {policy : Policy} {host : HostState} {s : State}
    {cid : Nat} {cursor cursor' : Vdbe.Cursor}
    (hinv : StateInv policy host s)
    (hcur : s.cursors cid = some cursor)
    (htab : cursor'.table = cursor.table) :
    StateInv policy host (s.setCursor cid cursor') := by
  obtain ⟨hcid, db, root, hauth, hfound⟩ := hinv.cursorsConfined cid cursor hcur
  exact stateInv_setCursor_authorized hinv hcid hauth (htab ▸ hfound)

private theorem stateInv_emit {policy : Policy} {host : HostState} {s : State}
    {first count : Nat}
    (hinv : StateInv policy host s)
    (hwidth : count ≤ policy.maxResultWidth) :
    StateInv policy host (s.emit first count) where
  registersConfined := hinv.registersConfined
  cursorsConfined := hinv.cursorsConfined
  rowsBounded := by
    intro row hrow
    simp only [Vdbe.State.emit, List.mem_append, List.mem_singleton] at hrow
    rcases hrow with hold | rfl
    · exact hinv.rowsBounded row hold
    · simpa [List.length_map, List.length_range] using hwidth

theorem execute_preserves_stateInv {policy : Policy} {codeSize : Nat} {host : HostState}
    {instr : Instruction} {s s' : State}
    (hwf : InstructionWf policy codeSize instr)
    (hinv : StateInv policy host s)
    (hexec : Vdbe.execute host.databases instr s = .ok s') :
    StateInv policy host s' := by
  cases instr with
  | init target =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact stateInv_jump hinv
  | goto target =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact stateInv_jump hinv
  | halt code =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact ⟨hinv.registersConfined, hinv.cursorsConfined, hinv.rowsBounded⟩
  | integer value destination =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact stateInv_advance (stateInv_write hinv hwf)
  | int64 value destination =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact stateInv_advance (stateInv_write hinv hwf)
  | string8 value destination =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact stateInv_advance (stateInv_write hinv hwf)
  | null first last =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact stateInv_advance (stateInv_writeNull hinv)
  | copy source destination additional =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      have hdest1 : 1 ≤ destination := hwf.2.2.1
      have hdest2 : destination + additional ≤ policy.maxRegisters := hwf.2.2.2
      have hbounds :
          additional + 1 = 0 ∨ (1 ≤ destination ∧ destination + (additional + 1) - 1 ≤ policy.maxRegisters) :=
        Or.inr ⟨hdest1, by omega⟩
      exact stateInv_advance (stateInv_copyRegisters (additional + 1) source destination s hinv hbounds)
  | openRead cursor root database =>
      simp only [Vdbe.execute] at hexec
      cases hdb : host.databases database root with
      | none =>
          simp [hdb] at hexec
      | some table =>
          simp only [hdb, Except.ok.injEq] at hexec
          subst hexec
          exact stateInv_advance (stateInv_setCursor_authorized hinv hwf.2 hwf.1 hdb)
  | rewind cursor target =>
      simp only [Vdbe.execute] at hexec
      cases hcur : s.cursors cursor with
      | none =>
          simp [hcur] at hexec
      | some c =>
          simp only [hcur] at hexec
          split at hexec
          · cases hexec
          · simp only [Except.ok.injEq] at hexec
            subst hexec
            exact stateInv_jump (stateInv_updateCursor hinv hcur rfl)
  | next cursor target =>
      simp only [Vdbe.execute] at hexec
      cases hcur : s.cursors cursor with
      | none =>
          simp [hcur] at hexec
      | some c =>
          simp only [hcur] at hexec
          split at hexec
          · cases hexec
          · cases hrem : c.remaining with
            | none =>
                simp [hrem] at hexec
            | some rem =>
                simp only [hrem, Except.ok.injEq] at hexec
                subst hexec
                exact stateInv_jump (stateInv_updateCursor hinv hcur rfl)
  | column cursor col destination =>
      simp only [Vdbe.execute] at hexec
      cases hcur : s.cursors cursor with
      | none =>
          simp [hcur] at hexec
      | some c =>
          simp only [hcur] at hexec
          cases hrow : c.current? with
          | none =>
              simp [hrow] at hexec
          | some entry =>
              simp only [hrow, Except.ok.injEq] at hexec
              subst hexec
              exact stateInv_advance (stateInv_write hinv hwf.2)
  | rowid cursor destination =>
      simp only [Vdbe.execute] at hexec
      cases hcur : s.cursors cursor with
      | none =>
          simp [hcur] at hexec
      | some c =>
          simp only [hcur] at hexec
          cases hrow : c.current? with
          | none =>
              simp [hrow] at hexec
          | some entry =>
              simp only [hrow] at hexec
              split at hexec
              · simp only [Except.ok.injEq] at hexec
                subst hexec
                exact stateInv_advance (stateInv_write hinv hwf.2)
              · cases hexec
  | resultRow first count =>
      simp only [Vdbe.execute, Except.ok.injEq] at hexec
      subst hexec
      exact stateInv_advance (stateInv_emit hinv hwf.1)
  | seekRowid cursor target keyRegister =>
      simp only [Vdbe.execute] at hexec
      cases hcur : s.cursors cursor with
      | none =>
          simp [hcur] at hexec
      | some c =>
          simp only [hcur] at hexec
          cases hreg : s.registers keyRegister with
          | integer key =>
              simp only [hreg] at hexec
              split at hexec
              · cases hexec
              · simp only [Except.ok.injEq] at hexec
                subst hexec
                exact stateInv_jump (stateInv_updateCursor hinv hcur rfl)
          | null | real _ | text _ | blob _ =>
              simp [hreg] at hexec

theorem stepEffects_allowed {policy : Policy} {program : Program}
    (hwf : WellFormed policy program) (s : State) (outcome : Except Fault State) :
    ∀ e ∈ stepEffects program s outcome, e.Allowed policy := by
  intro e he
  unfold stepEffects at he
  by_cases hhalt : s.halted.isSome
  · simp [hhalt] at he
  · simp only [hhalt, Bool.false_eq_true, ↓reduceIte] at he
    cases hpc : program[s.pc]? with
    | none =>
        simp [hpc] at he
    | some instr =>
        have hiwf := hwf s.pc instr hpc
        simp only [hpc] at he
        cases instr with
        | openRead cursor root database =>
            cases outcome with
            | ok _ =>
                simp only [List.mem_singleton] at he
                subst he
                exact hiwf.1
            | error _ =>
                simp only [List.mem_singleton] at he
                subst he
                exact hiwf.1
        | resultRow first count =>
            cases outcome with
            | ok _ =>
                simp only [List.mem_singleton] at he
                subst he
                simpa [Effect.Allowed, List.length_map, List.length_range] using hiwf.1
            | error _ =>
                simp at he
        | init _ | goto _ | halt _ | integer _ _ | int64 _ _ | string8 _ _
        | null _ _ | copy _ _ _ | rewind _ _ | next _ _ | column _ _ _
        | rowid _ _ | seekRowid _ _ _ =>
            simp at he

theorem stepIsolated_isolation {policy : Policy} {host : HostState} {program : Program}
    {s : State} (hwf : WellFormed policy program) (hinv : StateInv policy host s) :
    (∀ e ∈ (stepIsolated host program s).1, e.Allowed policy) ∧
    (∀ host' s', (stepIsolated host program s).2 = .ok (host', s') →
      host' = host ∧ StateInv policy host' s' ∧ step host.databases program s = .ok s') ∧
    (∀ err, (stepIsolated host program s).2 = .error err →
      step host.databases program s = .error err) := by
  refine ⟨stepEffects_allowed hwf s _, ?_, ?_⟩
  · intro host' s' hok
    unfold stepIsolated at hok
    cases hstep : step host.databases program s with
    | error err =>
        simp [hstep, Except.map] at hok
    | ok after =>
        simp only [hstep, Except.map, Except.ok.injEq, Prod.mk.injEq] at hok
        rcases hok with ⟨rfl, rfl⟩
        refine ⟨rfl, ?_, rfl⟩
        unfold step Vdbe.step at hstep
        by_cases hhalt : s.halted.isSome
        · simp [hhalt] at hstep
        · simp only [hhalt, Bool.false_eq_true, ↓reduceIte] at hstep
          cases hpc : program[s.pc]? with
          | none =>
              simp [hpc] at hstep
          | some instr =>
              simp only [hpc] at hstep
              exact execute_preserves_stateInv (hwf s.pc instr hpc) hinv hstep
  · intro err herr
    unfold stepIsolated at herr
    cases hstep : step host.databases program s with
    | ok after =>
        simp [hstep, Except.map] at herr
    | error e =>
        simp only [hstep, Except.map, Except.error.injEq] at herr
        subst herr
        rfl

theorem runIsolated_result (host : HostState) (program : Program) (fuel : Nat) (s : State) :
    (runIsolated host program fuel s).result = run host.databases program fuel s := by
  induction fuel generalizing s with
  | zero =>
      by_cases hhalt : s.halted.isSome <;> simp [runIsolated, run, Vdbe.run, hhalt]
  | succ fuel ih =>
      by_cases hhalt : s.halted.isSome
      · simp [runIsolated, run, Vdbe.run, hhalt]
      · cases hstep : step host.databases program s <;>
          simp [runIsolated, stepIsolated, run, Vdbe.run, Except.map, hhalt, hstep, ih]

theorem runIsolated_host_unchanged (host : HostState) (program : Program) (fuel : Nat) (s : State) :
    (runIsolated host program fuel s).host = host := by
  induction fuel generalizing s with
  | zero =>
      by_cases hhalt : s.halted.isSome <;> simp [runIsolated, hhalt]
  | succ fuel ih =>
      by_cases hhalt : s.halted.isSome
      · simp [runIsolated, hhalt]
      · cases hstep : step host.databases program s <;>
          simp [runIsolated, stepIsolated, Except.map, hhalt, hstep, ih]

theorem runIsolated_isolation {policy : Policy} {host : HostState} {program : Program}
    (hwf : WellFormed policy program) (fuel : Nat) {s : State}
    (hinv : StateInv policy host s) :
    (∀ e ∈ (runIsolated host program fuel s).events, e.Allowed policy) ∧
    (runIsolated host program fuel s).host = host ∧
    StateInv policy (runIsolated host program fuel s).host (runIsolated host program fuel s).result.state ∧
    (runIsolated host program fuel s).result = run host.databases program fuel s := by
  induction fuel generalizing s with
  | zero =>
      by_cases hhalt : s.halted.isSome
      · simp [runIsolated, run, Vdbe.run, Vdbe.RunResult.state, hhalt, hinv]
      · simp [runIsolated, run, Vdbe.run, Vdbe.RunResult.state, hhalt, hinv]
  | succ fuel ih =>
      by_cases hhalt : s.halted.isSome
      · simp [runIsolated, run, Vdbe.run, Vdbe.RunResult.state, hhalt, hinv]
      · obtain ⟨heff, hok, _⟩ := stepIsolated_isolation hwf hinv
        cases hstep : (stepIsolated host program s).2 with
        | error fault =>
            simp only [runIsolated, hhalt, Bool.false_eq_true, ↓reduceIte, hstep, Vdbe.RunResult.state]
            refine ⟨heff, trivial, hinv, ?_⟩
            have hraw : step host.databases program s = .error fault := by
              unfold stepIsolated at hstep
              cases hst : step host.databases program s <;> simp [hst, Except.map] at hstep ⊢
              exact hstep
            simp [run, Vdbe.run, hhalt, hraw]
        | ok pair =>
            rcases pair with ⟨host', after⟩
            obtain ⟨rfl, hinv', hraw⟩ := hok host' after hstep
            obtain ⟨hevRest, hhostRest, hinvRest, hresRest⟩ := ih hinv'
            simp only [runIsolated, hhalt, Bool.false_eq_true, ↓reduceIte, hstep]
            refine ⟨?_, hhostRest, hinvRest, ?_⟩
            · intro e he
              rcases List.mem_append.mp he with h1 | h2
              · exact heff e h1
              · exact hevRest e h2
            · simp [run, Vdbe.run, hhalt, hraw, hresRest]

theorem admitAndRun_isolation (policy : Policy) (host : HostState)
    (raw : Vdbe.RawProgram) (fuel : Nat) :
    match admitAndRun policy host raw fuel with
    | .rejected _ => True
    | .executed out =>
        (∀ e ∈ out.events, e.Allowed policy) ∧
        out.host = host ∧
        StateInv policy out.host out.result.state ∧
        ∃ program, admitProgram policy raw = .ok program ∧
          out.result = run host.databases program fuel initial := by
  unfold admitAndRun
  cases hadm : admitProgram policy raw with
  | error reason =>
      trivial
  | ok program =>
      have hwf := admitProgram_wellFormed hadm
      have hinv := stateInv_initial policy host
      obtain ⟨heff, hhost, hinv', hres⟩ := runIsolated_isolation hwf fuel hinv
      exact ⟨heff, hhost, hinv', program, rfl, hres⟩

theorem admitAndRun_no_denied_effects {policy : Policy} {host : HostState}
    {raw : Vdbe.RawProgram} {fuel : Nat} {out : RunOutcome}
    (hexec : admitAndRun policy host raw fuel = .executed out) :
    ∀ e ∈ out.events,
      (∀ db root, e ≠ .writeTable db root) ∧
      (∀ name, e ≠ .attachDb name) ∧
      (∀ path, e ≠ .loadExtension path) ∧
      (∀ op, e ≠ .hostEscape op) ∧
      (∀ db root found, e = .readTable db root found → policy.canRead db root = true) ∧
      (∀ cells, e = .emitRow cells → cells.length ≤ policy.maxResultWidth) := by
  have hiso := admitAndRun_isolation policy host raw fuel
  rw [hexec] at hiso
  intro e he
  have hall := hiso.1 e he
  cases e with
  | readTable db root found =>
      refine ⟨(by intro _ _ h; cases h), (by intro _ h; cases h), (by intro _ h; cases h),
        (by intro _ h; cases h), ?_, (by intro _ h; cases h)⟩
      intro db' root' found' h
      cases h
      exact hall
  | emitRow cells =>
      refine ⟨(by intro _ _ h; cases h), (by intro _ h; cases h), (by intro _ h; cases h),
        (by intro _ h; cases h), (by intro _ _ _ h; cases h), ?_⟩
      intro cells' h
      cases h
      exact hall
  | writeTable _ _ => exact False.elim hall
  | attachDb _ => exact False.elim hall
  | loadExtension _ => exact False.elim hall
  | hostEscape _ => exact False.elim hall

end Silmaril.Proofs.Machine.SQLite.VirtualMachine.Isolation
