module

public import Silmaril.Containers.Lps.Defs
public import Silmaril.Containers.Machine.Thms
public import Silmaril.Process.LPS.Probes.Oracle
import Silmaril.Proofs.Containers.Lps.Basic

/-!
# The LPS adapter: theorems

PROVED (standard axioms). Proofs are in `Silmaril.Proofs.Containers.Lps`.

**Programs that only exit.** For a snapshot that satisfies `ExitOnly snap k` (every admissible
launch, for every flag oracle and allocation limit, has only finite, error-free LPS executions
whose events are stop events and which halt with status `k`; no reachable configuration is
about to create a task; and some launch is admissible):

* `runs_eq`: every run of the adapter under `seqPolicy` is `done [] (exited (k mod 256))`;
* `run_exists`: that run exists, so the statement is not vacuous.

The proof follows the adapter step by step: from a configuration satisfying the invariant every
adapter step is an internal LPS step (no events to emit, no unsupported event, no error, no task
creation), adapter paths are finite (an infinite one would be an infinite LPS execution, which
`Omni.Exec` excludes), and no state is stuck (`Omni.Exec` has a step at every running
configuration). Clone freedom is a separate hypothesis because `Omni.Exec` constrains traces and
outcomes, not intermediate states, and LPS models `fork` as a successful step.

**General soundness** (`runs_sound`), over any system call table `sp` (the adapter is
`lpsWith sp`; `lps` is `lpsWith Probes.spec`): if every admissible launch has only finite,
error-free LPS executions with supported events whose container events and exit status satisfy
`G` (`EvPost`), and none reaches a task-creation request (`Sound sp snap G`), then no run has
undefined behaviour and every exiting run satisfies `G`.

**Programs with bounded output.** For a snapshot that satisfies `Emits snap k w` (as `ExitOnly`,
but the LPS events of every execution are read by the adapter as container events that form a
prefix of `w`, and `w` has no inputs):

* `runs_prefix`: every run under `seqPolicy` is `done t (exited (k mod 256))` with `t` a prefix of
  `w`: no undefined behaviour, no blocking, no divergence, no other stop;
* `run_of_star`: a chosen finite LPS execution of an admissible launch (for example the full
  write of a probe, built with the kit's run rules) is a run, with its container events.

`ExitOnly snap k` is `Emits snap k []` (`emits_of_exitOnly`), and `runs_eq`, `run_exists` are its
special case. The invariant now also carries the events emitted and pending, so an adapter state
that still has events to emit can neither stop nor wait (outputs are not inputs).

**Clone freedom along a probe's execution.** `noClone_instr`, `noClone_trap`, `noClone_write`,
`noClone_exit` mirror the probe kit's execution rules (`Probes.Probe.oexec_*`) with the same side
conditions, so a probe's unique-successor chain proves `NoCloneFrom` with the same tactic script
(`noclone_instr`, `noclone_trap`, `noclone_write`, `noclone_exit`).
-/

public section

namespace Silmaril.Containers.Lps

open Silmaril.Containers Silmaril.Containers.Mach
open Silmaril.Process.LPS Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes

theorem runs_eq {snap : X86Launch.Snapshot} {k : Word} (h : ExitOnly snap k) (b : Beh Ev)
    (hb : lps.Run seqPolicy snap b) : b = .done [] (.exited (k.toNat % 256).toUInt8) :=
  Silmaril.Proofs.Containers.Lps.runs_eq h b hb

theorem run_exists {snap : X86Launch.Snapshot} {k : Word} (h : ExitOnly snap k) :
    lps.Run seqPolicy snap (.done [] (.exited (k.toNat % 256).toUInt8)) :=
  Silmaril.Proofs.Containers.Lps.run_exists_exit h

/-- **General soundness, over any system call table `sp`**: under `Sound sp snap G`, no run has
undefined behaviour, and every run that exits with status `c` has events `t` with `G t k` for a
status word `k` with `c = k mod 256` (partial correctness: blocking and divergence are not
excluded). -/
theorem runs_sound {sp : Sys SyscallEffect} {snap : X86Launch.Snapshot} {G : List Ev → Word → Prop}
    (h : Sound sp snap G) (b : Beh Ev) (hb : (lpsWith sp).Run seqPolicy snap b) :
    Spec.noUB b ∧ ∀ t c, b = .done t (.exited c) → ∃ k, c = (k.toNat % 256).toUInt8 ∧ G t k :=
  Silmaril.Proofs.Containers.Lps.runs_sound h b hb

/-- A chosen finite LPS execution under `sp`, with supported events and no task creation, is a
run. -/
theorem run_of_starWith {sp : Sys SyscallEffect} {snap : X86Launch.Snapshot} {o : Oracle}
    {limit : Int} {en : ExecEntry} {inp : ProcInput}
    (ha : Problems.CoreutilsLite.Admissible o snap en inp) {tr : List Event}
    {c' : Silmaril.Process.LPS.Config (isaOf o)} {u : List Ev} {code : Word}
    (hn : NoCloneFromWith sp snap.image.segments (X86Launch.init (isaOf o) snap en limit inp))
    (hs : Star snap.image.segments sp noFilter (X86Launch.init (isaOf o) snap en limit inp) tr c')
    (hu : mapEvs tr = some u) (hh : c'.model.halted = some code) (hk : c'.model.killedBy = none) :
    (lpsWith sp).Run seqPolicy snap (.done u (.exited (code.toNat % 256).toUInt8)) :=
  Silmaril.Proofs.Containers.Lps.run_of_starWith ha hn hs hu hh hk

/-- **Runs of a program with bounded output**: every run under `seqPolicy` exits with status
`k mod 256` after emitting a prefix of `w`. -/
theorem runs_prefix {snap : X86Launch.Snapshot} {k : Word} {w : List Ev} (h : Emits snap k w)
    (b : Beh Ev) (hb : lps.Run seqPolicy snap b) :
    ∃ t, t <+: w ∧ b = .done t (.exited (k.toNat % 256).toUInt8) :=
  Silmaril.Proofs.Containers.Lps.runs_prefix h b hb

/-- **A chosen LPS execution is a run**: a finite execution of an admissible launch to a halted,
unkilled configuration, whose events the adapter supports, is the run emitting their container
events. -/
theorem run_of_star {snap : X86Launch.Snapshot} {k : Word} {w : List Ev} (h : Emits snap k w)
    {o : Oracle} {limit : Int} {en : ExecEntry} {inp : ProcInput}
    (ha : Problems.CoreutilsLite.Admissible o snap en inp) {tr : List Event}
    {c' : Silmaril.Process.LPS.Config (isaOf o)} {u : List Ev} {code : Word}
    (hs : Star snap.image.segments Probes.spec noFilter
      (X86Launch.init (isaOf o) snap en limit inp) tr c')
    (hu : mapEvs tr = some u) (hh : c'.model.halted = some code) (hk : c'.model.killedBy = none) :
    lps.Run seqPolicy snap (.done u (.exited (code.toNat % 256).toUInt8)) :=
  Silmaril.Proofs.Containers.Lps.run_of_star h ha hs hu hh hk

/-- Octets written to standard output, then an exit: one standard-output event per octet, and
the exit is the run's stop, not an event. -/
theorem mapEvs_stdout_exit (c : Word) (fs : Silmaril.Process.LPS.Fs.FileSystem) (ds : List Byte) :
    mapEvs (ds.map (.writeEv 1) ++ [.exitEv c fs]) = some (ds.map fun b => .stdout [UInt8.ofBitVec b]) :=
  Silmaril.Proofs.Containers.Lps.mapEvs_stdout_exit c fs ds

theorem emits_of_exitOnly {snap : X86Launch.Snapshot} {k : Word} (h : ExitOnly snap k) :
    Emits snap k [] :=
  Silmaril.Proofs.Containers.Lps.emits_of_exitOnly h

theorem noClone_instr (P : Probe) (oracle : Oracle) [Probe.Checked P] {off len : Nat}
    {instruction : Silmaril.X86.Ext.Instr} {core core' : Silmaril.X86.State} {counter : Nat}
    {model : Silmaril.Process.LPS.Model} (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core P.mem0 len = .ok core' P.mem0)
    (rest : NoCloneFrom P.segs (P.ocfg oracle core' none counter model)) :
    NoCloneFrom P.segs (P.ocfg oracle core none counter model) :=
  Silmaril.Proofs.Containers.Lps.noClone_instr P oracle running lazy rip fits two notSyscall
    decoded exec rest

theorem noClone_trap (P : Probe) (oracle : Oracle) [Probe.Checked P] {off : Nat}
    {core : Silmaril.X86.State} {counter : Nat} {model : Silmaril.Process.LPS.Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (rest : NoCloneFrom P.segs (P.ocfg oracle (Probe.complete core (oracle counter))
      (some (core.read .rax)) (counter + 1) model)) :
    NoCloneFrom P.segs (P.ocfg oracle core none counter model) :=
  Silmaril.Proofs.Containers.Lps.noClone_trap P oracle running lazy rip two isSyscall rest

theorem noClone_exit (P : Probe) (oracle : Oracle) {core : Silmaril.X86.State} {n : Word}
    {counter : Nat} {model : Silmaril.Process.LPS.Model} (number : n = 60)
    (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysIn core n) = false) :
    NoCloneFrom P.segs (P.ocfg oracle core (some n) counter model) :=
  Silmaril.Proofs.Containers.Lps.noClone_exit P oracle number running clear

theorem noClone_write (P : Probe) (oracle : Oracle) [Probe.Checked P] {core : Silmaril.X86.State}
    {n : Word} {counter : Nat} {model : Silmaril.Process.LPS.Model} {off count : Nat} {ch : Word}
    (number : n = 1) (running : model.halted = none) (lazy : model.vmLazy = [])
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (buffer : core.read .rsi = BitVec.ofNat 64 (P.base + off))
    (modeled : modeledRwRangeWith accessOkbX86 (core.read .rsi) (core.read .rdx) = true)
    (nonzeroCount : core.read .rdx ≠ 0)
    (clear : NativeX86.All.boundarySuspect 1 (P.sysIn core n) = false)
    (clamp : rwCountClamp (core.read .rdx) = count)
    (clampWord : (zw (rwCountClamp (core.read .rdx))).toNat = count)
    (fits : off + count ≤ P.size) (nonempty : (P.bytes.drop off).take count ≠ [])
    (rest : ∀ ds, Probe.WritePrefix ((P.bytes.drop off).take count) ds →
      NoCloneFrom P.segs (P.ocfg oracle (Probe.resume core (lenWord ds)) none counter model)) :
    NoCloneFrom P.segs (P.ocfg oracle core (some n) counter model) :=
  Silmaril.Proofs.Containers.Lps.noClone_write P oracle number running lazy lookup nonzero buffer
    modeled nonzeroCount clear clamp clampWord fits nonempty rest

macro "noclone_instr " off:term:max len:term:max instr:term:max : tactic =>
  `(tactic|
    (apply Silmaril.Containers.Lps.noClone_instr _ _ (off := $off) (len := $len) (instruction := $instr)
      <;> oprobe_sides))

macro "noclone_trap " off:term:max : tactic =>
  `(tactic| (apply Silmaril.Containers.Lps.noClone_trap _ _ (off := $off) <;> oprobe_sides))

macro "noclone_write " off:term:max count:term:max : tactic =>
  `(tactic| (apply Silmaril.Containers.Lps.noClone_write _ _ (off := $off) (count := $count)
    <;> oprobe_sides))

macro "noclone_exit" : tactic =>
  `(tactic| (apply Silmaril.Containers.Lps.noClone_exit <;> oprobe_sides))

end Silmaril.Containers.Lps
