module

public import Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.History.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.Thms
public import Silmaril.Machine.SqliteVfs.PageRead.ReadTrace.Thms
public import Silmaril.Machine.SqliteVfs.PageRead.ReadFrame.Thms
public import Silmaril.Machine.SqliteVfs.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.PageRead.WriteExtent.History

open Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.History (DisjointWrite)
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)
open Silmaril.Machine.SqliteVfs.PageRead.WriteExtent (presentCount disjoint_write_agrees_iff)

private theorem successful_write_extent {capacity : Nat} {before after : FileState}
    {handle : Handle} {offset : Int} {data : Bytes}
    (write : readWrite capacity before (.write handle offset data) = (.ok (), after)) :
    after.bytes.length = max before.bytes.length (offset.toNat + data.length) ∧
      after.mode handle = before.mode handle := by
  have law := (readWrite_lawful capacity).2.2.write before handle offset data
  change backing .readWrite capacity before (.write handle offset data) = (.ok (), after) at write
  simp only [Response, id, write] at law
  split at law
  · cases law.1
  · cases law.1
  · split at law
    · split at law
      · rw [law.2]
        exact ⟨overwrite_length _ _ _, rfl⟩
      · cases law.1
    · cases law.1

private theorem disjoint_write_history_frame {capacity : Nat}
    {before after : FileState} {trace : Trace} (page : Page)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (covered : ∀ exchange ∈ trace, DisjointWrite page exchange) :
    presentCount before page ≤ presentCount after page ∧
      after.mode page.handle = before.mode page.handle ∧
      (presentCount before page = presentCount after page → AgreesOnPage before after page) := by
  induction valid with
  | nil => exact ⟨Nat.le_refl _, rfl, fun _ _ _ => rfl⟩
  | @cons before middle after request response rest next _ ih =>
    have guard := covered ⟨request, response⟩ (by simp)
    have first : presentCount before page ≤ presentCount middle page ∧
        middle.mode page.handle = before.mode page.handle ∧
        (presentCount before page = presentCount middle page → AgreesOnPage before middle page) := by
      cases guard with
      | write offset data apart =>
        have write := successful_write_extent next
        have grows : presentCount before page ≤ presentCount middle page :=
          Nat.le_min.mpr ⟨Nat.min_le_left _ _,
            Nat.le_trans (Nat.min_le_right _ _) (Nat.sub_le_sub_right (write.1 ▸ Nat.le_max_left _ _) _)⟩
        exact ⟨grows, write.2, (disjoint_write_agrees_iff page next apart).mpr⟩
    have later := ih (fun exchange member => covered exchange (List.mem_cons_of_mem _ member))
    refine ⟨Nat.le_trans first.1 later.1, later.2.1.trans first.2.1, ?_⟩
    intro same
    have firstEq := Nat.le_antisymm first.1 (by simpa only [← same] using later.1)
    have nextEq := firstEq.symm.trans same
    exact fun i within => (first.2.2 firstEq i within).trans (later.2.2 nextEq i within)

theorem disjoint_write_history_agrees_iff {capacity : Nat}
    {before after : FileState} {trace : Trace} (page : Page)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (covered : ∀ exchange ∈ trace, DisjointWrite page exchange) :
    (AgreesOnPage before after page ↔ presentCount before page = presentCount after page) ∧
      after.mode page.handle = before.mode page.handle := by
  have frame := disjoint_write_history_frame page valid covered
  exact ⟨⟨WriteExtent.presentCount_eq_of_agreement page, frame.2.2⟩, frame.2.1⟩

private theorem presentCount_stays_or_full_of_disjoint_write {capacity : Nat}
    {before after : FileState} (page : Page) {offset : Int} {data : Bytes}
    (write : readWrite capacity before (.write page.handle offset data) = (.ok (), after))
    (apart : page.offset + page.size ≤ offset.toNat ∨ offset.toNat + data.length ≤ page.offset) :
    presentCount before page = presentCount after page ∨ presentCount after page = page.size := by
  have size := (successful_write_extent write).1
  unfold presentCount
  rcases apart with right | left
  · right
    omega
  · left
    omega

private theorem presentCount_stays_or_full_of_history {capacity : Nat}
    {before after : FileState} {trace : Trace} (page : Page)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (covered : ∀ exchange ∈ trace, DisjointWrite page exchange) :
    presentCount before page = presentCount after page ∨ presentCount after page = page.size := by
  induction valid with
  | nil => exact .inl rfl
  | @cons before middle after request response rest next _ ih =>
    have step := covered ⟨request, response⟩ (by simp)
    have first : presentCount before page = presentCount middle page ∨ presentCount middle page = page.size := by
      cases step with
      | write offset data apart => exact presentCount_stays_or_full_of_disjoint_write page next apart
    rcases ih (fun exchange member => covered exchange (List.mem_cons_of_mem _ member)) with equal | full
    · rcases first with same | full
      · exact .inl (same.trans equal)
      · exact .inr (equal.symm.trans full)
    · exact .inr full

/-- Over these writes, preserving the complete typed reply is equivalent to
preserving the number of present bytes in the requested page. -/
theorem disjoint_write_history_reply_iff {capacity : Nat}
    {before after : FileState} {trace : Trace} (page : Page)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (covered : ∀ exchange ∈ trace, DisjointWrite page exchange)
    (admitted : page.Admitted) (live : (before.mode page.handle).isNone = false) :
    (readWrite capacity before page.request).1 = (readWrite capacity after page.request).1 ↔
      presentCount before page = presentCount after page := by
  obtain ⟨agreesIff, mode⟩ := disjoint_write_history_agrees_iff page valid covered
  have afterLive : (after.mode page.handle).isNone = false := by
    rw [mode]
    exact live
  constructor
  · intro reply
    rcases presentCount_stays_or_full_of_history page valid covered with equal | full
    · exact equal
    · by_contra changed
      have positive : 0 < page.size := by
        have := admitted.2.2.1
        omega
      have beforeShort : ¬ page.offset + page.size ≤ before.bytes.length := by
        unfold presentCount at changed full
        omega
      have afterFull : page.offset + page.size ≤ after.bytes.length := by
        unfold presentCount at full
        omega
      have read (file : FileState) (isLive : (file.mode page.handle).isNone = false) :
          (readWrite capacity file page.request).1 = readBacking file.bytes page.offset page.size := by
        simp [Page.request, readWrite, backing, isLive, admitted.2]
        rfl
      rw [read before live, read after afterLive] at reply
      simp [readBacking, beforeShort, afterFull] at reply
  · intro equal
    exact ReadFrame.lawful_read_reply_agrees (readWrite_lawful capacity).2.1
      (readWrite_lawful capacity).2.1 before after page admitted live afterLive (agreesIff.mpr equal)

theorem reads_around_disjoint_write_history {capacity : Nat}
    {before after : FileState} {trace : Trace} (page : Page)
    (valid : Trace.Valid (readWrite capacity) before trace after)
    (covered : ∀ exchange ∈ trace, DisjointWrite page exchange)
    (extent : presentCount before page = presentCount after page)
    (admitted : page.Admitted) (live : (before.mode page.handle).isNone = false) :
    let read : Exchange := ⟨page.request, (readWrite capacity before page.request).1⟩
    Trace.Valid (readWrite capacity) before ([read] ++ trace ++ [read]) after := by
  obtain ⟨iff, mode⟩ := disjoint_write_history_agrees_iff page valid covered
  exact ReadTrace.reads_around_trace (readWrite_lawful capacity).2.1 valid page admitted live
    (by rw [mode]; exact live) (iff.mpr extent)

end Silmaril.Proofs.Machine.SqliteVfs.PageRead.WriteExtent.History
