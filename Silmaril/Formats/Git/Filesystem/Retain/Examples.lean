module

import Silmaril.Formats.Git.Filesystem.Retain.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Cbor.Drisl.Cid.Defs
meta import Silmaril.Formats.Git.Arena.Defs
meta import Silmaril.Formats.Git.Filesystem.Retain.Defs
meta import Batteries.Data.Except

/-! Executable fixtures for the hash-only and retained lanes. `mock` is a weak
test function, so no fixture depends on collision resistance. -/

namespace Silmaril.Formats.Git.Filesystem.Retain.Examples

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Arena (CasLane Read)
open Silmaril.Formats.Git.Filesystem
open Silmaril.Formats.Dasl.Prolly (ByteKey)

private abbrev Item := Σ mode : EntryMode, Object ByteKey String Unit mode.kind
private abbrev Snapshot := Object ByteKey String Unit .tree

private def emptyDir : Directory ByteKey Item := ⟨∅, fun key => False.elim (Finset.notMem_empty _ key.property)⟩

private def toTree (dir : Directory ByteKey Item) : Snapshot :=
  .tree dir.keys (fun key => (dir.get key).1) (fun key => (dir.get key).2)

private def body : ByteArray := "echo ok\n".toByteArray
private def dirKey : ByteKey := Dasl.utf8Key "dir"

private def mock (wire : ByteArray) : Digest :=
  let stamp := wire.toList.foldl (fun total byte => total * 65599 + byte.toUInt64) (0 : UInt64)
  ⟨(List.ofFn fun index : Fin 8 => (stamp >>> (8 * index.val.toUInt64)).toUInt8) ++ List.replicate 24 0, by simp⟩

/-- A non-UTF-8 executable name below a directory, an empty directory and a symlink. -/
private def nested : Snapshot :=
  let inner := toTree (emptyDir.insert [255] ⟨.file .executable, .blob body⟩)
  let withDir := emptyDir.insert dirKey ⟨.directory, inner⟩
  let withEmpty := withDir.insert (Dasl.utf8Key "empty") ⟨.directory, toTree emptyDir⟩
  toTree (withEmpty.insert (Dasl.utf8Key "link") ⟨.file .symlink, .blob "dir/".toByteArray⟩)

/-- Thirty-three one-byte names: one branch over two leaves at width 32. -/
private def wide : Snapshot :=
  toTree ((List.range 33).foldl (fun dir offset =>
    dir.insert [Fin.ofNat 256 (offset + 1)] ⟨.file .regular, .blob body⟩) emptyDir)

private def gitlink : Snapshot := toTree (emptyDir.insert dirKey ⟨.gitlink, .ref .commit "external-commit"⟩)
private def badName : Snapshot := toTree (emptyDir.insert [0] ⟨.file .regular, .blob body⟩)

private def sameRoot (tree : Snapshot) : Bool := rootCid mock tree == (stage mock tree).map Image.name

#guard sameRoot nested && sameRoot wide && (rootCid mock nested).isOk
#guard sameRoot gitlink && rootCid mock gitlink == .error (.gitlink dirKey)
#guard sameRoot badName && rootCid mock badName == .error (.component [0])
#guard rootCid mock (toTree emptyDir) == directoryCid mock ⟨∅, fun key => False.elim (Finset.notMem_empty _ key.property)⟩

private def none? : Cid → Option ByteArray := fun _ => none

/-- Keep the root and the leaf selected by key `[1]`; drop the other leaf and the blob. -/
private def partialCase : Except String Unit := do
  let image ← (stage mock wide).mapError fun fault => reprStr fault
  let .ok full := image.publish none? | .error "full publication conflicts"
  let .ok (.branch 1 [(_, first), (_, last)]) := dirReader mock (Store.ofPublished full) image.name |
    .error "fixture is not one branch over two leaves"
  let keep : Cid → Bool := fun cid => cid == image.name || cid == first
  let .ok part := image.publishRetained keep none? | .error "retained publication conflicts"
  let owed := image.promised keep
  let blob := address mock .raw body
  let found : Except ReadFault (Option (Entry Cid)) := .ok (some ⟨.file .regular, blob⟩)
  let check (message : String) (claim : Bool) : Except String Unit := if claim then .ok () else .error message
  check "same root on every lane" (rootCid mock wide == .ok image.name)
  check "the dropped leaf and blob are owed" (owed.contains last && owed.contains blob && !owed.contains first)
  check "retained path answers" (lookupChildRouted mock (Store.ofPartial part owed) 2 image.name [1] == found)
  check "a full store gives the same answer" (lookupChildRouted mock (Store.ofPublished full) 2 image.name [1] == found)
  check "owed block is deferred, not absent"
    (lookupChildRouted mock (Store.ofPartial part owed) 2 image.name [33] == .error (.deferred last))
  check "with no promise the block is missing, not absent"
    (lookupChildRouted mock (Store.ofPartial part []) 2 image.name [33] == .error (.block (.missing last)))
  check "a retained separator still proves absence"
    (lookupChildRouted mock (Store.ofPartial part owed) 2 image.name [34] == .ok none)
  check "entry metadata does not make dropped bytes available"
    (readVerified mock (Store.ofPartial part owed) .raw blob == .deferred &&
      readVerified mock (Store.ofPublished full) .raw blob == .found body)
  let .ok same := image.publishRetained (fun _ => false) part | .error "empty retention failed"
  check "hash-only retention leaves the store unchanged"
    (image.writes.all fun write => same write.1 == part write.1)
  check "hash-only root is unreadable until bytes arrive"
    (readVerified mock (Store.ofPartial none? []) .object image.name == .missing)
  let .ok healed := image.publish part | .error "completing a partial import conflicts"
  check "completing the import restores the dropped answer"
    (lookupChildRouted mock (Store.ofPublished healed) 2 image.name [33] == found)
  match image.publishRetained keep (fun cid => if cid == image.name then some ByteArray.empty else none) with
  | .ok _ => .error "retained publication overwrote different bytes"
  | .error cid => check "conflict names the root" (cid == image.name)

#guard partialCase == .ok ()

end Silmaril.Formats.Git.Filesystem.Retain.Examples
