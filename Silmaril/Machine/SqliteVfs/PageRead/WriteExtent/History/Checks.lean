module

import Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.History.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.History

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)
open Silmaril.Machine.SqliteVfs.PageRead.WriteExtent (presentCount)

private def handle : Handle := ⟨0⟩
private def page : Page := ⟨handle, 2, 3⟩
private def start : FileState := ⟨[1, 2, 3, 10, 11], some .readWrite, 0⟩
private def inBetween : FileState := ⟨[1, 99, 3, 10, 11], some .readWrite, 0⟩
private def afterLeft : FileState := ⟨[1, 99, 77, 10, 11], some .readWrite, 0⟩
private def afterGrowth : FileState := ⟨[1, 99, 77, 10, 11, 0, 90], some .readWrite, 0⟩
private def left : Trace := [⟨.write handle 1 [99], .ok ()⟩, ⟨.write handle 2 [77], .ok ()⟩]
private def growth : Trace := left ++ [⟨.write handle 6 [90], .ok ()⟩]

private theorem leftValid : Trace.Valid (readWrite 16) start left afterLeft :=
  .cons (middle := inBetween) rfl (.cons rfl (.nil afterLeft))

private theorem growthValid : Trace.Valid (readWrite 16) start growth afterGrowth :=
  .cons (middle := inBetween) rfl (.cons (middle := afterLeft) rfl (.cons rfl (.nil afterGrowth)))

private theorem leftCovered (exchange : Exchange) (member : exchange ∈ left) :
    DisjointWrite page exchange := by
  simp [left] at member
  rcases member with rfl | rfl
  · exact .write 1 [99] (.inr (by decide))
  · exact .write 2 [77] (.inr (by decide))

private theorem growthCovered (exchange : Exchange) (member : exchange ∈ growth) :
    DisjointWrite page exchange := by
  simp [growth] at member
  rcases member with kept | rfl
  · exact leftCovered exchange kept
  · exact .write 6 [90] (.inl (by decide))

example :
    let read : Exchange := ⟨page.request, .shortRead [10, 11, 0]⟩
    Trace.Valid (readWrite 16) start ([read] ++ left ++ [read]) afterLeft :=
  reads_around_disjoint_write_history page leftValid leftCovered rfl (by decide) rfl

example : (readWrite 16 start page.request).1 = .shortRead [10, 11, 0] ∧
    (readWrite 16 afterGrowth page.request).1 = .ok [10, 11, 0] ∧
    ¬ AgreesOnPage start afterGrowth page := by
  refine ⟨rfl, rfl, ?_⟩
  intro agrees
  have counts := (disjoint_write_history_agrees_iff page growthValid growthCovered).1.mp agrees
  change 2 = 3 at counts
  contradiction

example : (readWrite 16 start page.request).1 = (readWrite 16 afterLeft page.request).1 :=
  (disjoint_write_history_reply_iff page leftValid leftCovered (by decide) rfl).mpr rfl

example : (readWrite 16 start page.request).1 ≠ (readWrite 16 afterGrowth page.request).1 := by
  intro same
  have equal := (disjoint_write_history_reply_iff page growthValid growthCovered (by decide) rfl).mp same
  exact (by decide : presentCount start page ≠ presentCount afterGrowth page) equal

private def afterFullWrite : FileState := ⟨[1, 99, 77, 10, 11, 0, 91], some .readWrite, 0⟩
private def fullWrite : Trace := [⟨.write handle 6 [91], .ok ()⟩]

example : (readWrite 16 afterGrowth page.request).1 = (readWrite 16 afterFullWrite page.request).1 := by
  have valid : Trace.Valid (readWrite 16) afterGrowth fullWrite afterFullWrite :=
    .cons rfl (.nil afterFullWrite)
  have covered (exchange : Exchange) (member : exchange ∈ fullWrite) : DisjointWrite page exchange := by
    have equal : exchange = ⟨.write handle 6 [91], .ok ()⟩ := by simpa [fullWrite] using member
    subst exchange
    exact .write 6 [91] (.inl (by decide))
  exact (disjoint_write_history_reply_iff page valid covered (by decide) rfl).mpr rfl

example : readWrite 16 start (.write handle 6 []) = (.error .invalidRange, start) := rfl

example : ¬ (⟨handle, 2, 0⟩ : Page).Admitted := by decide

example : Trace.Valid (readWrite 16) start
    [⟨page.request, .shortRead [10, 11, 0]⟩, ⟨page.request, .shortRead [10, 11, 0]⟩] start :=
  reads_around_disjoint_write_history page (.nil start) (by simp) rfl (by decide) rfl

private def shrunk : FileState := ⟨[1, 2, 3, 10], some .readWrite, 0⟩
private def resized : FileState := ⟨[1, 2, 3, 10, 0], some .readWrite, 0⟩

example :
    Trace.Valid (readWrite 16) start
      [⟨.truncate handle 4, .ok ()⟩, ⟨.truncate handle 5, .ok ()⟩] resized ∧
      presentCount start page = presentCount resized page ∧
      ¬ AgreesOnPage start resized page := by
  refine ⟨.cons (middle := shrunk) rfl (.cons rfl (.nil resized)), rfl, ?_⟩
  intro agrees
  have mismatch := agrees 1 (by decide)
  change some (11 : UInt8) = some 0 at mismatch
  exact (by decide : some (11 : UInt8) ≠ some 0) mismatch

private def zeroAtEnd : FileState := ⟨[1, 2, 3, 10, 0], some .readWrite, 0⟩

example : Trace.Valid (readWrite 16) zeroAtEnd
    [⟨.truncate handle 4, .ok ()⟩] shrunk ∧
    (readWrite 16 zeroAtEnd page.request).1 = .shortRead [10, 0, 0] ∧
    (readWrite 16 shrunk page.request).1 = .shortRead [10, 0, 0] ∧
    presentCount zeroAtEnd page ≠ presentCount shrunk page :=
  ⟨.cons rfl (.nil shrunk), rfl, rfl, by decide⟩

#print axioms disjoint_write_history_agrees_iff
#print axioms reads_around_disjoint_write_history
#print axioms disjoint_write_history_reply_iff

end Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.History
