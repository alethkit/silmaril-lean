module

public import Silmaril.X86.EntryRelay.Defs
public import Silmaril.X86.Open.Thms
public import Silmaril.X86.FnContract.Thms
public import Silmaril.X86.Ext.Lemmas

@[expose] public section
namespace Silmaril.Proofs.X86.EntryRelay

open Silmaril.X86 Silmaril.X86.EntryRelay

theorem step_to_suffix {entry : MState} {body : List Byte}
    (loaded : Ext.Loaded entry.memory entry.core.rip (jumpBytes ++ body)) :
    Open.step entry = some (suffixEntry entry) := by
  refine Open.step_of_listed (o := 0) (l := 2) (i := .base (.jmp8 0))
    loaded (by simp) (by simp [jumpBytes]) ?_ ?_
  · change Open.decode jumpBytes = some (.base (.jmp8 0), 2)
    decide +kernel
  · change Ext.exec (.jmp8 0) entry.core entry.memory = _
    have len : (Ext.Instr.jmp8 0).length = 2 := by decide
    rw [Ext.exec_jmp8, len]
    simp

private theorem entry_not_returned (entry : MState) : ¬ FnContract.Returned Open.isa entry entry := by
  intro returned
  have stack := returned.2
  change entry.core.read .rsp = entry.core.read .rsp + 8#64 at stack
  have zero : (0 : BitVec 64) = 8 := by
    simpa using congrArg (fun sp => sp - entry.core.read .rsp) stack
  contradiction

/-- Starting through the checked jump or at its suffix has exactly the same
first-return states. Code memory, return address and stack are shared. -/
theorem firstReturn_iff_suffix {entry final : MState} {body : List Byte}
    (loaded : Ext.Loaded entry.memory entry.core.rip (jumpBytes ++ body)) :
    FnContract.FirstReturn Open.isa entry final ↔
      FnContract.FirstReturn Open.isa (suffixEntry entry) final := by
  have hop := step_to_suffix loaded
  have same (s : MState) :
      FnContract.Returned Open.isa entry s ↔ FnContract.Returned Open.isa (suffixEntry entry) s := Iff.rfl
  constructor
  · rintro ⟨steps, ended⟩
    cases steps with
    | refl => exact (entry_not_returned entry ended).elim
    | step _ actual rest =>
      change Open.step entry = some _ at actual
      rw [hop] at actual
      cases Option.some.inj actual
      exact ⟨FnContract.runsIn_mono (fun s hn hr => hn ((same s).2 hr)) rest, (same _).1 ended⟩
  · rintro ⟨steps, ended⟩
    refine ⟨.step (entry_not_returned entry) hop ?_, (same _).2 ended⟩
    exact FnContract.runsIn_mono (fun s hn hr => hn ((same s).1 hr)) steps

/-- The literal `mov eax,3054001; ret` body. This fixture inserts a designed
entry relay before it, independently of either compiler artifact. -/
private def versionBody : List Byte := [0xb8, 0xb1, 0x99, 0x2e, 0, 0xc3]

private def code : List Byte := jumpBytes ++ versionBody

private def stackBytes : List Byte := Silmaril.Machine.LittleEndian.encodeWords [0x9000]

private def stackBacking : Silmaril.Process.ByteMemory :=
  Silmaril.Process.Memory.install ∅ 0x8008 stackBytes

private def fixtureMemory : Silmaril.Process.Memory :=
  ⟨[⟨0x1000, code.length, ⟨true, false, true⟩⟩, ⟨0x8008, 8, ⟨true, true, false⟩⟩],
    Silmaril.Process.Memory.install stackBacking 0x1000 code⟩

private def fixtureEntry : MState :=
  ⟨{ regs := fun r => if r = .rsp then 0x8008 else 0,
     rip := 0x1000, flags := ⟨none, none, none, none, none, none⟩ }, fixtureMemory⟩

private def fixtureMove : MState :=
  ⟨{ (suffixEntry fixtureEntry).core.write .rax 3054001 with rip := 0x1007 }, fixtureMemory⟩

private def fixtureFinal : MState :=
  ⟨{ fixtureMove.core.write .rsp 0x8010 with rip := 0x9000 }, fixtureMemory⟩

private theorem loadedFixture : Ext.Loaded fixtureMemory 0x1000 code := by
  exact Silmaril.Process.Memory.readWith_eq _ _ _ _ (by decide)
    (fun i hi => Silmaril.Process.Memory.install_get stackBacking 0x1000 code i hi)

private theorem loadedSuffix : Ext.Loaded fixtureMemory 0x1002 versionBody :=
  loadedFixture.fetchBytes_sub (offset := 2) (len := 6) (by decide) (by decide)

private theorem stackRead : fixtureMemory.readBytes 0x8008 8 = some stackBytes := by
  change fixtureMemory.readWith .read 0x8008 stackBytes.length = some stackBytes
  refine Silmaril.Process.Memory.readWith_eq fixtureMemory .read 0x8008 stackBytes (by decide) ?_
  intro i hi
  change (Silmaril.Process.Memory.install stackBacking 0x1000 code).get? (0x8008 + i) = _
  have outside : 0x1000 + code.length ≤ 0x8008 + i := by
    change 0x1008 ≤ 0x8008 + i
    omega
  rw [Silmaril.Process.Memory.install_outside _ _ _ _ (.inr outside)]
  exact Silmaril.Process.Memory.install_get ∅ 0x8008 stackBytes i hi

private theorem retAddress : FnContract.retOf (suffixEntry fixtureEntry).core fixtureMemory = 0x9000 := by
  change ((fixtureMemory.readBytes 0x8008 8).bind wordOfBytes?).getD 0 = 0x9000
  rw [stackRead]
  rfl
example : Open.decode [0xeb, 5] = some (.base (.jmp8 5), 2) := by decide +kernel

private theorem fixtureSuffixReturns : FnContract.FirstReturn Open.isa (suffixEntry fixtureEntry) fixtureFinal := by
  have stepMov : Open.step (suffixEntry fixtureEntry) = some fixtureMove := by
    refine Open.step_of_listed (o := 0) (l := 5) (i := .base (.movI32 .rax 3054001))
      loadedSuffix (by rfl) (by decide) (by decide +kernel) ?_
    change Ext.exec (.movI32 .rax 3054001) (suffixEntry fixtureEntry).core fixtureMemory = _
    rw [Ext.exec_movI32]
    rfl
  have stepRet : Open.step fixtureMove = some fixtureFinal := by
    refine Open.step_of_listed (o := 5) (l := 1) (i := .base .ret)
      loadedSuffix (by rfl) (by decide) (by decide +kernel) ?_
    have readable : fixtureMemory.readBytes (fixtureMove.core.read .rsp).toNat 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [0x9000]) := stackRead
    change Ext.exec .ret fixtureMove.core fixtureMemory = _
    have rsp : fixtureMove.core.read .rsp = 0x8008 := rfl
    simp [Ext.exec_ret, Insn.exec, popWord_of_readBytes readable, rsp]
  refine ⟨.step (entry_not_returned _) stepMov (.step ?_ stepRet (.refl _)), ⟨retAddress.symm, rfl⟩⟩
  intro returned
  have stack := returned.2
  change (0x8008 : Word) = 0x8010 at stack
  contradiction

/-- Concrete first returns with and without the extra machine jump. -/
private theorem fixture_returns :
    FnContract.FirstReturn Open.isa fixtureEntry fixtureFinal ∧
    FnContract.FirstReturn Open.isa (suffixEntry fixtureEntry) fixtureFinal ∧
    fixtureFinal.core.read .rax = 3054001 ∧ fixtureFinal.memory = fixtureEntry.memory :=
  by
    refine ⟨?_, fixtureSuffixReturns, rfl, rfl⟩
    exact (firstReturn_iff_suffix (entry := fixtureEntry) (body := versionBody) loadedFixture).2
      fixtureSuffixReturns

theorem distinct_version_witness :
    let body : List Byte := [0xb8, 0xb1, 0x99, 0x2e, 0, 0xc3]
    ∃ entry final : MState,
      Ext.Loaded entry.memory entry.core.rip (jumpBytes ++ body) ∧
      Ext.Loaded entry.memory (suffixEntry entry).core.rip body ∧
      jumpBytes ++ body ≠ body ∧
      FnContract.FirstReturn Open.isa entry final ∧
      FnContract.FirstReturn Open.isa (suffixEntry entry) final ∧
      final.core.read .rax = 3054001 ∧ final.memory = entry.memory :=
  ⟨fixtureEntry, fixtureFinal, loadedFixture, loadedSuffix, by decide, fixture_returns⟩

end Silmaril.Proofs.X86.EntryRelay
