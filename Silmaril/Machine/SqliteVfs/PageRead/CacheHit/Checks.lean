module

import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Thms
meta import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
meta import Silmaril.Machine.SqliteVfs.PageRead.Defs
meta import Silmaril.Machine.SqliteVfs.Defs
meta import Silmaril.Formats.Sqlite.Defs

namespace Silmaril.Machine.SqliteVfs.PageRead.CacheHit

open Silmaril.Formats.Sqlite

private def cache : Cache := fun slot => if slot = 0 then some .vacant else none
private def smallPage : Page := ⟨⟨0⟩, 2, 2⟩
private def before : FileState := ⟨[10, 20, 30, 40, 50], some .readOnly, 0⟩
private def current : FileState := ⟨[99, 20, 30, 40], some .readOnly, 0⟩

private theorem samePage : AgreesOnPage before current smallPage := by
  intro i inside
  change i < 2 at inside
  have index : i = 0 ∨ i = 1 := by omega
  rcases index with rfl | rfl <;> rfl

example :
    let original := fill (readOnly 8) before cache 0 smallPage
    let fresh := fill (readOnly 8) current cache 0 smallPage
    ∃ bytes, lookup original.cache 0 smallPage = some bytes ∧
      fresh = ⟨.ok bytes, current, cache.install 0 smallPage bytes, [⟨smallPage.request, .ok bytes⟩]⟩ :=
  hit_after_fill_matches_refetch 8 before current cache 0 smallPage rfl
    (by decide) rfl rfl (by decide) samePage

example : lookup (fill (readOnly 8) before cache 0 smallPage).cache
    0 {smallPage with handle := ⟨1⟩} = none := rfl

private def leaf (aliasType amount : UInt8) : Bytes :=
  [13, 0, 0, 0, 1, 1, 250, 0, 1, 250] ++ List.replicate 496 0 ++ [4, 7, 3, aliasType, 1, amount]

private def emptyLeaf : Bytes :=
  [13, 0, 0, 0, 0, 2, 0, 0] ++ List.replicate 504 0

private def page : Page := ⟨⟨0⟩, 1, 512⟩
private def file (bytes : Bytes) : FileState := ⟨bytes, some .readOnly, 0⟩
private def scan : Vdbe.Program :=
  #[.openRead 0 2 0, .rewind 0 6, .column 0 0 1, .column 0 1 2,
    .resultRow 1 2, .next 0 2, .halt 0]

private abbrev Observation := Option (Option (List (List Value) × Option Nat))

private def observe (result : Option (Option Vdbe.RunResult)) : Observation :=
  result.map (Option.map fun run => (run.state.rows, run.state.halted))

private def checkBoth (original current : Bytes) (hit fresh : Observation) : Bool :=
  let installed := fill (readOnly 1024) (file original) cache 0 page
  let refetch := fill (readOnly 1024) (file current) cache 0 page
  decide (observe (runHit? installed.cache 0 page 0 0 2 scan 16 .initial) = hit) &&
    decide (observe (runPage? refetch.result.toOption 0 0 2 scan 16 .initial) = fresh)

private def typedRow (amount : Int64) : Observation :=
  some (some ([[.integer 7, .integer amount]], some 0))

-- The bounded evaluator comparisons are separate from the kernel theorems.
#guard checkBoth (leaf 0 5 ++ [42]) (leaf 0 5) (typedRow 5) (typedRow 5)
#guard checkBoth (leaf 8 5) (leaf 8 5) (some none) (some none)
#guard checkBoth emptyLeaf emptyLeaf (some (some ([], some 0))) (some (some ([], some 0)))
#guard checkBoth (leaf 0 5) (leaf 0 6) (typedRow 5) (typedRow 6)
#guard (runHit? cache 0 page 0 0 2 scan 16 .initial).isNone

#print axioms lookup_after_success
#print axioms hit_after_fill_matches_refetch
#print axioms runHit_matches_refetch

end Silmaril.Machine.SqliteVfs.PageRead.CacheHit
