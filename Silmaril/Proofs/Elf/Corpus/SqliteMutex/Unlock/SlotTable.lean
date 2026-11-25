module

public import Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding.Defs
import Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding.Thms
import Silmaril.Elf.Link.Dyn.Elf.Thms

public section

namespace Silmaril.Proofs.Elf.Corpus.SqliteMutex.Unlock.SlotTable

open Silmaril.Elf.Link
open Silmaril.Elf.Link.DynElf
open Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding
open Silmaril.X86.Link (Blob)

local notation "Sqlite" => Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.F

private theorem run_mapM {α β : Type} (oracle : Nat → Nat → Option Nat) (f : α → Rd β)
    (items : List α) :
    (items.mapM f).run oracle = items.mapM (fun x => (f x).run oracle) := by
  unfold List.mapM
  let g := fun x => (f x).run oracle
  suffices h : ∀ (remaining : List α) (seen : List β),
      (List.mapM.loop f remaining seen).run oracle = List.mapM.loop g remaining seen by
    exact h items []
  intro remaining seen
  induction remaining generalizing seen with
  | nil => rfl
  | cons x xs ih =>
    change (Rd.bind (f x) (fun y => List.mapM.loop f xs (y :: seen))).run oracle =
      ((f x).run oracle).bind (fun y => List.mapM.loop g xs (y :: seen))
    rw [Rd.run_bind]
    simp only [ih]

private theorem mem_mapM {α β : Type} {g : α → Option β} {inputs : List α} {outputs : List β}
    {input : α} {output : β} (path : inputs.mapM g = some outputs)
    (member : input ∈ inputs) (computed : g input = some output) :
    output ∈ outputs := by
  induction inputs generalizing outputs with
  | nil => simp at member
  | cons next rest ih =>
    rw [List.mapM_cons] at path
    cases result : g next with
    | none => simp [result] at path
    | some value =>
      cases tail : rest.mapM g with
      | none => simp [result, tail] at path
      | some values =>
        simp [result, tail] at path
        subst outputs
        rcases List.mem_cons.mp member with equal | inRest
        · subst next
          rw [computed] at result
          exact List.mem_cons.mpr (.inl (Option.some.inj result))
        · exact List.mem_cons.mpr (.inr (ih tail inRest))

private theorem mapM_none_of_mem {α β : Type} {g : α → Option β} {items : List α} {bad : α}
    (member : bad ∈ items) (failed : g bad = none) :
    items.mapM g = none := by
  induction items with
  | nil => simp at member
  | cons next rest ih =>
    rw [List.mapM_cons]
    rcases List.mem_cons.mp member with same | inRest
    · subst next
      simp [failed]
    · cases g next <;> simp [ih inRest]

private theorem table_contains {dynamic : Elf.DynInfo} {regular : List Elf.Rela}
    (parsed : Dyn.frun Sqlite (Elf.relaTable dynamic Elf.DT_RELA
      ((dynamic.tag Elf.DT_RELASZ).getD 0 / 24)) = some regular)
    (witness : Dyn.frun Sqlite (Rd.bind (Rd.ofOption (dynamic.tagOff Elf.DT_RELA)) (fun base =>
      Rd.bind (Rd.guard (1170 < ((dynamic.tag Elf.DT_RELASZ).getD 0 / 24))) (fun _ =>
        Elf.rela (base + 24 * 1170)))) = some absoluteReloc) :
    absoluteReloc ∈ regular := by
  unfold Dyn.frun at parsed witness
  rw [Rd.run_bind] at witness
  obtain ⟨base, offset, checked⟩ := Option.bind_eq_some_iff.mp witness
  rw [Rd.run_bind] at checked
  obtain ⟨_, guard, read⟩ := Option.bind_eq_some_iff.mp checked
  have index : 1170 < (dynamic.tag Elf.DT_RELASZ).getD 0 / 24 := by
    unfold Rd.guard at guard
    split at guard
    · assumption
    · cases guard
  unfold Elf.relaTable at parsed
  rw [ite_eq_right (by omega)] at parsed
  change (Rd.bind (Rd.ofOption (dynamic.tagOff Elf.DT_RELA)) (fun base =>
    (List.range ((dynamic.tag Elf.DT_RELASZ).getD 0 / 24)).mapM
      (fun index => Elf.rela (base + 24 * index)))).run (blobRead Sqlite) = some regular at parsed
  rw [Rd.run_bind, offset, Option.bind_some, run_mapM] at parsed
  exact mem_mapM parsed (List.mem_range.mpr index) read

theorem no_sqlite_slot_table (resolver : Dyn.Resolver) (lazy : Bool) (dynamic : Elf.DynInfo)
    (headers : Dyn.finfo Sqlite = some dynamic) :
    Dyn.slotsWith resolver lazy Sqlite dynamic = none := by
  have witness := absolute_relocation
  change (Rd.bind Elf.dynInfo (fun info =>
    Rd.bind (Rd.ofOption (info.tagOff Elf.DT_RELA)) (fun base =>
      Rd.bind (Rd.guard (1170 < ((info.tag Elf.DT_RELASZ).getD 0 / 24))) (fun _ =>
        Elf.rela (base + 24 * 1170))))).run (blobRead Sqlite) = some absoluteReloc at witness
  rw [Rd.run_bind, show Elf.dynInfo.run (blobRead Sqlite) = some dynamic from headers,
    Option.bind_some] at witness
  unfold Dyn.slotsWith
  cases relas : Dyn.frun Sqlite (Elf.relas dynamic) with
  | none => rfl
  | some tables =>
    obtain ⟨regular, jumps⟩ := tables
    have parsed : Dyn.frun Sqlite (Elf.relaTable dynamic Elf.DT_RELA
        ((dynamic.tag Elf.DT_RELASZ).getD 0 / 24)) = some regular := by
      change (Rd.bind (Rd.guard (dynamic.tag Elf.DT_RELR = none)) (fun _ =>
        Rd.bind (Elf.relaTable dynamic Elf.DT_RELA ((dynamic.tag Elf.DT_RELASZ).getD 0 / 24)) (fun rs =>
          Rd.bind (Elf.relaTable dynamic Elf.DT_JMPREL ((dynamic.tag Elf.DT_PLTRELSZ).getD 0 / 24))
            (fun js => Rd.pure (rs, js))))).run (blobRead Sqlite) = some (regular, jumps) at relas
      rw [Rd.run_bind] at relas
      obtain ⟨_, _, relas⟩ := Option.bind_eq_some_iff.mp relas
      rw [Rd.run_bind] at relas
      obtain ⟨rs, parsed, relas⟩ := Option.bind_eq_some_iff.mp relas
      rw [Rd.run_bind] at relas
      obtain ⟨js, _, pair⟩ := Option.bind_eq_some_iff.mp relas
      cases pair
      exact parsed
    have member := table_contains parsed witness
    have failed : regular.mapM (fun r => (Dyn.relocVal resolver Sqlite dynamic r).map
        (fun w => (r.off, w))) = none :=
      mapM_none_of_mem member (by rw [absolute_has_no_model_value]; rfl)
    simp [failed]

theorem sqlite_cannot_head_exe_loaded (scopeTail : List Blob) (bases : List Silmaril.X86.Word)
    (ifunc : Silmaril.X86.Word → Option Silmaril.X86.Word) (lazy : Bool)
    (resolver : Silmaril.X86.Word) (memory : Silmaril.Process.Memory) :
    ¬ Dyn.ExeLoaded (Sqlite :: scopeTail) bases ifunc lazy resolver memory := by
  rintro ⟨file, _, dynamic, table, _, first, _, headers, _, slots, _, _⟩
  cases first
  have noTable := no_sqlite_slot_table (Dyn.resolve (Sqlite :: scopeTail)) lazy dynamic headers
  have computed : Dyn.slotsWith (Dyn.resolve (Sqlite :: scopeTail)) lazy Sqlite dynamic = some table :=
    slots
  rw [noTable] at computed
  cases computed

end Silmaril.Proofs.Elf.Corpus.SqliteMutex.Unlock.SlotTable
