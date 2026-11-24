module

public import Silmaril.Formats.Git.Filesystem.Retain.Defs
public import Silmaril.Formats.Git.Filesystem.Routed.Thms
public import Silmaril.Formats.Git.Filesystem.Writer.Thms
import Silmaril.Proofs.Formats.Git.Filesystem.Retain

public section

namespace Silmaril.Formats.Git.Filesystem

open Silmaril.Semantics
open Formats.Dasl.Prolly (ByteKey Fault route)
open Arena (CasLane Read)

variable {hash : Hash} {Ref Meta : Type} {kind : Kind}

theorem directoryCid_eq_stageDirectory (hash : Hash) (directory : ByteDirectory) :
    directoryCid hash directory = (stageDirectory hash directory).map Image.name :=
  Proofs.Formats.Git.Filesystem.directoryCid_eq_stageDirectory hash directory

/-- Hash-only naming and persistent emission agree on the root and on every
fault. Neither side assumes that `hash` is injective. -/
theorem rootCid_eq_stage (hash : Hash) (tree : Object ByteKey Ref Meta kind) :
    rootCid hash tree = (stage hash tree).map Image.name :=
  Proofs.Formats.Git.Filesystem.rootCid_eq_stage hash tree

theorem Image.retained_all (image : Image hash kind) : image.retained (fun _ => true) = image.writes := by
  simp [Image.retained]

theorem Image.publishRetained_all (image : Image hash kind) (store : Cid → Option ByteArray) :
    image.publishRetained (fun _ => true) store = image.publish store := by
  simp [Image.publishRetained, Image.publish, Image.retained]

/-- Keeping nothing leaves the store unchanged: the hash-only lane is the empty retention. -/
theorem Image.publishRetained_none (image : Image hash kind) (store : Cid → Option ByteArray) :
    image.publishRetained (fun _ => false) store = .ok store := by
  simp [Image.publishRetained, Image.retained, Naming.admit]

/-- Every staged binding is either kept exactly or recorded as owed. -/
theorem Image.accounted (image : Image hash kind) (keep : Cid → Bool) {binding : Cid × ByteArray}
    (member : binding ∈ image.writes) : binding ∈ image.retained keep ∨ binding.1 ∈ image.promised keep :=
  Proofs.Formats.Git.Filesystem.accounted image keep member

theorem Image.publishRetained_bindings {image : Image hash kind} {keep : Cid → Bool}
    {before part : Cid → Option ByteArray} (published : image.publishRetained keep before = .ok part) :
    Naming.graph part = Naming.union (Naming.graph before) (Naming.listed (image.retained keep)) :=
  Naming.admit_eq_union published

/-- Wherever the full closure is admitted, every retained subset is admitted
and binds only bytes of the full result. -/
theorem Image.publishRetained_of_publish {image : Image hash kind} {before full : Cid → Option ByteArray}
    (published : image.publish before = .ok full) (keep : Cid → Bool) :
    ∃ part, image.publishRetained keep before = .ok part ∧ Naming.Subset (Naming.graph part) (Naming.graph full) :=
  Proofs.Formats.Git.Filesystem.publishRetained_of_publish published keep

theorem readVerified_ofPartial {part full : Cid → Option ByteArray} {promised : List Cid} {lane : CasLane}
    {name : Cid} {bytes : ByteArray} (subset : Naming.Subset (Naming.graph part) (Naming.graph full))
    (found : readVerified hash (Store.ofPartial part promised) lane name = .found bytes) :
    readVerified hash (Store.ofPublished full) lane name = .found bytes :=
  Proofs.Formats.Git.Filesystem.readVerified_ofPartial subset found

variable {directory : ByteDirectory} {image : Image hash .tree} {full part : Cid → Option ByteArray}
variable {promised : List Cid} {fuel : Nat} {key : ByteKey}

/-- A successful routed answer over a retained subset, including absence, is the
answer of the source directory. Dropped bytes can make a read fail, never lie. -/
theorem lookupChildRouted_partial_sound {result : Option (Entry Cid)}
    (staged : image.OfDirectory directory) (bounds : DirectoryBounds hash directory) (covered : image.Covered full)
    (subset : Naming.Subset (Naming.graph part) (Naming.graph full))
    (checked : lookupChildRouted hash (Store.ofPartial part promised) fuel image.name key = .ok result) :
    directory.ordered.lookup? key = result :=
  Proofs.Formats.Git.Filesystem.lookupChildRouted_partial_sound staged bounds covered subset checked

/-- A selected block that was promised and not kept is reported as deferred. -/
theorem lookupChildRouted_deferred {root cid : Cid} (valid : Dasl.validByteComponent key = true)
    (tagged : laneMatches .object cid = true) (dropped : part cid = none) (owed : cid ∈ promised)
    (faulted : route (dirReader hash (Store.ofPartial part promised)) policy.width key fuel none root =
      .error (.missing cid)) :
    lookupChildRouted hash (Store.ofPartial part promised) fuel root key = .error (.deferred cid) := by
  rw [lookupChildRouted, checkedChild_error valid faulted]
  simp [refineRead, Store.ofPartial, tagged, dropped, owed]

end Silmaril.Formats.Git.Filesystem
