module

public import Silmaril.Machine.SQLite.GlobalState.Defs
public import Silmaril.Machine.SqliteVfs.Defs
public import Std.Data.ExtTreeMap.Basic

@[expose] public section

namespace Silmaril.Machine.SQLite.GlobalState

/-- A caller-supplied slot in one kind's identity space. -/
structure LocalId (kind : ObjectKind) where
  slot : Nat
  deriving DecidableEq, Repr

/-- The disjoint sum of the local identity spaces. Equality compares both fields. -/
structure TaggedId where
  kind : ObjectKind
  slot : Nat
  deriving DecidableEq, Repr

instance : Hashable TaggedId where
  hash id := hash id.slot

def LocalId.tagged {kind : ObjectKind} (id : LocalId kind) : TaggedId := ⟨kind, id.slot⟩

def TaggedId.localId (id : TaggedId) : LocalId id.kind := ⟨id.slot⟩

/-- An element of `sqlite3.aDb`. Its position in that array can change. -/
structure BackendSlot where
  schemaName : String
  btree : Option (LocalId .btree)

structure ConnectionFields where
  vfs : Option (LocalId .vfs)
  firstStatement : Option (LocalId .statement)
  backends : List BackendSlot

/-- `Vdbe.ppVPrev` names the slot containing the incoming list link. The
connection for `connectionHead` is the statement's own connection. -/
inductive StatementLink where
  | connectionHead
  | predecessorNext (predecessor : LocalId .statement)

/-- A cache-local header slot, interpreted through the cursor or B-tree's Pager. -/
structure BufferedPageSlot where
  index : Nat
  deriving DecidableEq, Repr

/-- The B-tree variant of a VDBE cursor slot, with its inline `BtCursor`. -/
structure BtreeCursorFields where
  btree : LocalId .btree
  rootPage : Nat
  current : Option BufferedPageSlot
  parents : List BufferedPageSlot

structure StatementFields where
  connection : LocalId .connection
  incoming : StatementLink
  next : Option (LocalId .statement)
  sql : Option String
  btreeCursors : List (Option BtreeCursorFields)

/-- A usable blob borrows its private statement's B-tree cursor in slot zero. -/
structure BlobFields where
  connection : LocalId .connection
  statement : Option (LocalId .statement)
  schemaName : String
  column : Nat
  byteOffset : Nat
  byteCount : Nat

inductive BackupNotification where
  | detached
  | attached (next : Option (LocalId .backup))

/-- Public backup objects. The destination B-tree is acquired during step. -/
structure BackupFields where
  sourceConnection : LocalId .connection
  sourceBtree : LocalId .btree
  destinationConnection : LocalId .connection
  destinationSchema : String
  destinationBtree : Option (LocalId .btree)
  notification : BackupNotification

/-- Registration order is carried by the kind core's `VfsRoots`. -/
structure VfsFields where
  name : String
  osFileSize : Nat
  maxPathname : Nat

/-- Selected file observations. `openMode = none` allows allocated file
storage whose methods are not installed. -/
structure FileFields where
  path : Option String
  openMode : Option SqliteVfs.Mode

structure DirtyLinks where
  next : Option BufferedPageSlot
  previous : Option BufferedPageSlot

/-- Buffered header and page content. The slot and logical page number are
independent. The lower cache entry and B-tree page view share its storage. -/
structure BufferedPageFields where
  number : Nat
  bytes : SqliteVfs.Bytes
  references : Nat
  dirty : Option DirtyLinks

/-- Selected `PCache` state. Map keys are the cache-local slot indices. -/
structure PageCacheFields where
  pages : Std.ExtTreeMap Nat BufferedPageFields
  dirtyHead : Option BufferedPageSlot
  dirtyTail : Option BufferedPageSlot

structure PagerFields where
  vfs : LocalId .vfs
  cache : LocalId .pageCache
  mainFile : LocalId .file
  journal : LocalId .file
  subjournal : LocalId .file
  backupHead : Option (LocalId .backup)
  pageSize : Nat

/-- A scoped `BtShared` projection for a nonshared backend. -/
structure BtreeContent where
  pager : LocalId .pager
  pageOne : Option BufferedPageSlot

structure BtreeFields where
  connection : LocalId .connection
  content : BtreeContent
  sourceBackupCount : Nat

/-- The fields carried by the object kind. References classify their target
kind at the type level. Lifetime and referential integrity are separate. -/
def ObjectFields : ObjectKind → Type
  | .connection => ConnectionFields
  | .statement => StatementFields
  | .blob => BlobFields
  | .backup => BackupFields
  | .vfs => VfsFields
  | .file => FileFields
  | .pageCache => PageCacheFields
  | .pager => PagerFields
  | .btree => BtreeFields

end Silmaril.Machine.SQLite.GlobalState
