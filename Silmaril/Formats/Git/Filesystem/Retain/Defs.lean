module

public import Silmaril.Formats.Git.Filesystem.Routed.Defs
public import Silmaril.Formats.Git.Filesystem.Writer.Defs

/-! Hash-only naming and retained-subset publication for the tree-only filesystem
profile. One traversal fixes the root; retention chooses which staged bytes are kept. -/

@[expose] public section

namespace Silmaril.Formats.Git.Filesystem

open Formats.Dasl.Prolly (ByteKey)
open Silmaril.Semantics
open Arena (CasLane Read)

variable {Ref Meta : Type} {hash : Hash} {kind : Kind}

/-- Bottom-up directory naming with no serialized block returned or retained. -/
def directoryCid (hash : Hash) (directory : ShallowTree ByteKey Cid) : Except ImportFault Cid :=
  match (Prolly.build policy directory.ordered).rootName? (dirProfile hash).nameBlock? with
  | some root => .ok root
  | none => .error .encoding

/-- The hash-only lane: the checks, visiting order and faults of `stage`, carrying
one address per visited object instead of its bytes and descendants. -/
def rootCid (hash : Hash) : {kind : Kind} → Object ByteKey Ref Meta kind → Except ImportFault Cid
  | _, .blob bytes => .ok (address hash .raw bytes)
  | _, .ref kind _ => .error (.external kind)
  | _, .commit .. => .error .commit
  | _, .tree keys modes children => do
    let order := keys.attach.sort (· ≤ ·)
    let read ← Translate.Graph.scan (Value := fun _ : ↥keys => Cid) order fun child _ => do
      if !Dasl.validByteComponent child.val then throw (.component child.val)
      if modes child = .gitlink then throw (.gitlink child.val)
      rootCid hash (children child)
    let get := fun (child : ↥keys) => read child ((Finset.mem_sort _).mpr (Finset.mem_attach _ _))
    directoryCid hash ⟨keys, fun child => ⟨modes child, get child⟩⟩

/-- The staged bindings an importer keeps. The policy sees addresses only, so
it cannot change any name. Keeping nothing is the hash-only lane. -/
def Image.retained (image : Image hash kind) (keep : Cid → Bool) : Writes :=
  image.writes.filter fun write => keep write.1

/-- Addresses whose bytes were staged and dropped. A promise is a record that the
bytes are owed by some source. It is neither evidence nor availability. -/
def Image.promised (image : Image hash kind) (keep : Cid → Bool) : List Cid :=
  (image.writes.filter fun write => !keep write.1).map Prod.fst

def Image.publishRetained (image : Image hash kind) (keep : Cid → Bool) (store : Cid → Option ByteArray) :
    Except Cid (Cid → Option ByteArray) := Naming.admit store (image.retained keep)

/-- Read view of a partial import. A well-tagged name with no bytes is `deferred`
when a promise is recorded and `missing` otherwise. Neither is an absent entry. -/
def Store.ofPartial (store : Cid → Option ByteArray) (promised : List Cid) : Store := fun lane name =>
  if !laneMatches lane name then .invalid else
    match store name with
    | some wire => .found wire
    | none => if name ∈ promised then .deferred else .missing

end Silmaril.Formats.Git.Filesystem
