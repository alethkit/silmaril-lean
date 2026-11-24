module

public import SqliteWasmArtifactEntries
public import Silmaril.Wasm.Component.ChunkedDecode.Thms

@[expose] public section

namespace SqliteWasmArtifact

open Silmaril Silmaril.Wasm Silmaril.Wasm.Binary
open Core.Decode (Cursor DecodeM Sections readModule readSectionBody readU readVec sectionRank)
open Silmaril.Wasm.Component.Chunked (arr runAll)
open Silmaril.Wasm.Component.ChunkedDecode

/-- A non-custom section of the original, with its envelope and complete body read. -/
structure SectionRun (source : Packed.Cursor) (id : UInt8) (header start size : Nat)
    (update : Sections → Sections) : Prop where
  located : ((sectionSpans? source).bind fun spans => spans.lookup id.toNat) = some (start, size)
  identifier : source.source.toList[header]? = some id
  sizePrefix : readU 32 ⟨source.source.toByteArray, header + 1⟩ =
    .ok (size, ⟨source.source.toByteArray, start⟩)
  bound : start + size ≤ source.source.len
  nonCustom : id.toNat ≠ 0
  body : ∀ state, readSectionBody id.toNat state ⟨source.source.toByteArray, start⟩ =
    .ok (update state, ⟨source.source.toByteArray, start + size⟩)

/-- The checked section is a step in the ordinary Core module reader. -/
theorem SectionRun.step {source : Packed.Cursor} {id : UInt8} {header start size : Nat}
    {update : Sections → Sections} (checked : SectionRun source id header start size update)
    (fuel last : Nat) (state : Sections) (ordered : last < sectionRank id.toNat) :
    readModule.go (fuel + 1) last state ⟨source.source.toByteArray, header⟩ =
      readModule.go fuel (sectionRank id.toNat) (update state)
        ⟨source.source.toByteArray, start + size⟩ := by
  have fit := checked.bound
  rw [← source.source.length_toList source.wf] at fit
  exact go_known checked.identifier checked.sizePrefix fit checked.nonCustom ordered (checked.body state)

def sectionBytes (source : KBytes) (start stop : Nat) : List UInt8 :=
  (source.slice start (stop - start)).toList

private theorem slice_at {source : KBytes} (wf : source.wf = true) {start stop : Nat}
    (ordered : start ≤ stop) (fit : stop ≤ source.len) :
    At source.toList start (sectionBytes source start stop) ∧
      (sectionBytes source start stop).length = stop - start := by
  have bound : start + (stop - start) ≤ source.len := by omega
  have length := (source.slice start (stop - start)).length_toList (source.wf_slice _ _ wf bound)
  rw [source.len_slice] at length
  change (sectionBytes source start stop).length = stop - start at length
  refine ⟨⟨?_, ?_⟩, length⟩
  · rw [length]
    exact (source.toList_slice _ _ wf bound).symm
  · rwa [length, source.length_toList wf]

private theorem read_slice {α : Type} {source : KBytes} (wf : source.wf = true)
    {start stop : Nat} (ordered : start ≤ stop) (fit : stop ≤ source.len)
    {reader : DecodeM α} (frame : Frame reader) {out : α}
    (checked : runAll reader (sectionBytes source start stop) = some out) :
    reader ⟨source.toByteArray, start⟩ = .ok (out, ⟨source.toByteArray, stop⟩) := by
  have atStart := slice_at wf ordered fit
  have read := run_of_runAll frame checked atStart.1
  rwa [atStart.2, show start + (stop - start) = stop by omega] at read

/-- Check the section id, size and vector on bounded slices of the original artifact. -/
theorem sectionRun_of_vec {α : Type} {source : Packed.Cursor} {id : UInt8}
    {header start size : Nat} {reader : DecodeM α} {setField : Sections → List α → Sections}
    {entries : List α} (frame : Frame reader) (update : BodyOf id.toNat reader setField)
    (location : ((sectionSpans? source).bind fun spans => spans.lookup id.toNat) = some (start, size))
    (ordered : header + 1 ≤ start) (bound : start + size ≤ source.source.len) (nonCustom : id.toNat ≠ 0)
    (identifier : sectionBytes source.source header (header + 1) = [id])
    (sizePrefix : runAll (readU 32) (sectionBytes source.source (header + 1) start) = some size)
    (vector : runAll (readVec reader) (sectionBytes source.source start (start + size)) = some entries) :
    SectionRun source id header start size (fun state => setField state entries) := by
  have atIdentifier := (slice_at source.wf (Nat.le_succ header) (by omega)).1
  rw [identifier] at atIdentifier
  refine ⟨location, atIdentifier.get,
    read_slice source.wf ordered (by omega) (frame_readU 32) sizePrefix, bound, nonCustom, ?_⟩
  intro state
  exact update state _ _ _ (read_slice source.wf (Nat.le_add_right start size) bound (frame_readVec frame) vector)

end SqliteWasmArtifact
