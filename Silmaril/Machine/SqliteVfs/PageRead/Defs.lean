module

public import Silmaril.Machine.SqliteVfs.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead

/-- A one-based page on an already-open handle. The caller supplies the physical
page size from its file geometry. -/
structure Page where
  handle : Handle
  number : Nat
  size : Nat
  deriving DecidableEq, Repr

def Page.offset (page : Page) : Nat := (page.number - 1) * page.size

def Page.request (page : Page) : Request :=
  .read page.handle page.offset page.size

def Page.Admitted (page : Page) : Prop :=
  0 < page.number ∧ ReadRange page.offset page.size

instance (page : Page) : Decidable page.Admitted := by
  unfold Page.Admitted
  infer_instance

abbrev SlotId := Nat

inductive Slot where
  | vacant
  | resident (page : Page) (bytes : Bytes)
  deriving DecidableEq, Repr

/-- Absent slots are outside the caller's ownership. A vacant slot may be
filled once. A resident slot must be released by a separate operation. -/
abbrev Cache := SlotId → Option Slot

def Cache.install (cache : Cache) (target : SlotId) (page : Page) (bytes : Bytes) : Cache :=
  fun slot => if slot = target then some (.resident page bytes) else cache slot

inductive FillError where
  | unavailableSlot
  | invalidPage
  | shortRead
  | wrongLength
  | vfs (reason : Error)
  deriving DecidableEq, Repr

/-- Strict fill admits a complete page. The raw VFS exchange still records a
short-read buffer or a full response with the wrong length. -/
def accept (size : Nat) : ReadReply → Except FillError Bytes
  | .ok bytes => if bytes.length = size then .ok bytes else .error .wrongLength
  | .shortRead _ => .error .shortRead
  | .error reason => .error (.vfs reason)

structure Outcome (State : Type) where
  result : Except FillError Bytes
  file : State
  cache : Cache
  trace : Trace

/-- A serial cache miss. Local rejection makes no VFS call. After a call the
handler's state and exchange are retained even when the page is rejected. -/
def fill {State : Type} (handler : Handler State) (file : State) (cache : Cache)
    (target : SlotId) (page : Page) : Outcome State :=
  match cache target with
  | some .vacant =>
    if page.Admitted then
      let (reply, after) := handler file page.request
      let result := accept page.size reply
      let nextCache := match result with
        | .ok bytes => cache.install target page bytes
        | .error _ => cache
      ⟨result, after, nextCache, [⟨page.request, reply⟩]⟩
    else ⟨.error .invalidPage, file, cache, []⟩
  | _ => ⟨.error .unavailableSlot, file, cache, []⟩

end Silmaril.Machine.SqliteVfs.PageRead
