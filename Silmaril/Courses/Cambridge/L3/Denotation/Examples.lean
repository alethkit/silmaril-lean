module

import Silmaril.Courses.Cambridge.L3.Denotation
import Silmaril.Courses.Cambridge.L3.Examples

/-! # Checked L3 denotational observations -/

namespace Silmaril.Courses.Cambridge.L3.Denotation.Examples

open L3.Examples (recordLabels)

private def sumType : Ty := .sum .int .bool

private def members (i : recordLabels.Index) : Expr :=
  if i = 0 then .pair (.inl (.int 7) sumType) (.int 9) else .bool true

private def memberTypes (i : recordLabels.Index) : Ty :=
  if i = 0 then .prod sumType .int else .bool

private def dataProgram : Expr :=
  .snd (.project (.record recordLabels members) (recordLabels.label 0))

private theorem members_values (i : recordLabels.Index) : IsValue (members i) := by
  by_cases first : i = 0 <;> simp only [members, first, ite_true, ite_false]
  · exact .pair (.inl (.int 7)) (.int 9)
  · exact .bool true

example : HasType ∅ .empty dataProgram .int := by
  apply HasType.snd (A := sumType)
  have recordTyping : HasType ∅ .empty (.record recordLabels members)
      (.record recordLabels memberTypes) := by
    refine .record ?_
    intro i
    by_cases first : i = 0 <;> simp only [memberTypes, members, first, ite_true, ite_false]
    · exact .pair (.inl (.int 7)) (.int 9)
    · exact .bool true
  exact HasType.project (labels := recordLabels) 0 recordTyping

example : DataType.int.Observes dataProgram ∅ 9 ∅ := by
  apply (adequate_data (.snd (.project (.value (.record members_values))))).mpr
  refine .head (.sndStep (.projectValue (labels := recordLabels) 0 members_values)) ?_
  exact .single (.sndValue (.inl (.int 7)) (.int 9))

private def payloadLabel : RecordLabels := ⟨["payload"], by decide⟩

private def payloadType : DataType (.record payloadLabel (fun _ => .prod sumType .int)) :=
  .record (fun _ => .prod (.sum .int .bool) .int)

example : payloadType.Observes
    (.record payloadLabel (fun _ => .pair (.inl (.int 7) sumType) (.int 9)))
    ∅ (fun _ => (.inl 7, 9)) ∅ := by
  apply (adequate_data (.value (.record (fun _ => .pair (.inl (.int 7)) (.int 9))))).mpr
  exact .refl

-- Every fresh allocation branch produces the same ground answer and its own store.
private theorem read_new_cell (s : Store) (a : Loc) (fresh : a ∉ s) :
    DataType.int.Observes (.deref (.ref (.int 42))) s 42 (s.insert a (integer 42)) := by
  change Returns (denote (.ref (.int 42)) >>= read) s (integer 42) (s.insert a (integer 42))
  apply (returns_bind _ _ _ _ _).mpr
  refine ⟨address a, s.insert a (integer 42), ?_, ?_⟩
  · simp only [denote, pure_bind]
    exact ⟨a, fresh, rfl⟩
  · change (s.insert a (integer 42)).lookup a = some (integer 42) ∧ _
    exact ⟨by simp, rfl⟩

example :
    DataType.int.Observes (.deref (.ref (.int 42))) ∅ 42 ((∅ : Store).insert 0 (integer 42)) ∧
    DataType.int.Observes (.deref (.ref (.int 42))) ∅ 42 ((∅ : Store).insert 1 (integer 42)) ∧
    (∅ : Store).insert 0 (integer 42) ≠ (∅ : Store).insert 1 (integer 42) := by
  refine ⟨read_new_cell ∅ 0 Finmap.notMem_empty, read_new_cell ∅ 1 Finmap.notMem_empty, ?_⟩
  intro same
  have lookup := congrArg (fun s : Store => s.lookup 0) same
  simp [Finmap.lookup_insert_of_ne] at lookup

-- Allocation cannot return an address that was already in the input store.
example (s t : Store) (a : Loc) (present : a ∈ s) :
    ¬ Returns (denote (.ref (.int 42))) s (address a) t := by
  simp only [denote, pure_bind]
  intro returned
  change ∃ b, b ∉ s ∧ (address a, t) = (address b, s.insert b (integer 42)) at returned
  obtain ⟨b, fresh, equal⟩ := returned
  have same : a = b := Expr.loc.inj (congrArg Subtype.val (congrArg Prod.fst equal))
  exact fresh (same ▸ present)

-- Projection evaluates both record writes, retaining the second write's store.
example :
    DataType.unit.Observes L3.Examples.recordProgram ((∅ : Store).insert 0 L3.Examples.zero) ()
      ((∅ : Store).insert 0 L3.Examples.two) := by
  apply (adequate_data ?_).mpr L3.Examples.recordProgram_trace
  refine .project (.record ?_)
  intro i
  by_cases first : i = 0 <;> simp only [L3.Examples.writes, first, ite_true, ite_false]
  · exact .assign (.value (.loc 0)) (.value (.int 1))
  · exact .assign (.value (.loc 0)) (.value (.int 2))

private def flagStore : Store := (∅ : Store).insert 0 (boolean true)

private def flagTest : Expr := .deref (.loc 0)

private def allocateAndStop : Expr :=
  .seq (.assign (.ref (.int 11)) (.int 42)) (.assign (.loc 0) (.bool false))

private def allocateOnce : Expr := .loop flagTest allocateAndStop

private theorem allocateOnce_fragment : Fragment allocateOnce :=
  .loop (.deref (.value (.loc 0)))
    (.seq (.assign (.ref (.value (.int 11))) (.value (.int 42)))
      (.assign (.value (.loc 0)) (.value (.bool false))))

example : HasType ((∅ : LocTypes).insert 0 .bool) .empty allocateOnce .unit :=
  .loop (.deref (.loc (by simp))) (.seq (.assign (.ref (.int 11)) (.int 42))
    (.assign (.loc (by simp)) (.bool false)))

-- One iteration allocates, initializes the new cell, and clears the guard.
-- The final store depends on the fresh address selected during that iteration.
example (a : Loc) (fresh : a ∉ flagStore) :
    DataType.unit.Observes allocateOnce flagStore ()
      ((flagStore.insert a (integer 42)).insert 0 (boolean false)) := by
  apply (adequate_data allocateOnce_fragment).mpr
  let allocated := flagStore.insert a (integer 11)
  let written := flagStore.insert a (integer 42)
  let final := written.insert 0 (boolean false)
  have flagOn : flagStore.lookup 0 = some (boolean true) := by simp [flagStore]
  have allocatedStep : Step ⟨.ref (.int 11), flagStore⟩ ⟨.loc a, allocated⟩ :=
    .refValue (integer 11) fresh
  have writeStep : Step ⟨.assign (.loc a) (.int 42), allocated⟩ ⟨.skip, written⟩ := by
    change Step ⟨.assign (.loc a) (integer 42).val, allocated⟩ ⟨.skip, written⟩
    simpa only [allocated, written, Finmap.insert_insert] using
      (Step.assignValue (integer 42) (s := allocated) (loc := a) (by simp [allocated]))
  have clearStep : Step ⟨.assign (.loc 0) (.bool false), written⟩ ⟨.skip, final⟩ :=
    .assignValue (boolean false) (by simp [written, flagStore])
  have flagOff : final.lookup 0 = some (boolean false) := by simp [final]
  refine .head .while (.head (.ifStep (.derefValue flagOn)) (.head .ifTrue ?_))
  refine .head (.seqStep (.seqStep (.assignLeft allocatedStep))) ?_
  refine .head (.seqStep (.seqStep writeStep)) (.head (.seqStep .seqSkip) ?_)
  refine .head (.seqStep clearStep) (.head .seqSkip ?_)
  exact .head .while (.head (.ifStep (.derefValue flagOff)) (.single .ifFalse))

end Silmaril.Courses.Cambridge.L3.Denotation.Examples
