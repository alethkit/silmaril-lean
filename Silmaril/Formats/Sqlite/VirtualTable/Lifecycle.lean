module
public import Silmaril.Formats.Sqlite.VirtualTable.Defs

/-! Connection-local lifecycle for one eponymous-only read-only module and
one table instance. Handles are granted by xOpen and retired by xClose. -/
@[expose] public section
namespace Silmaril.Formats.Sqlite.VirtualTable

inductive Connection (width : Nat) where
  | registered (implementation : Module width) (nextHandle : Nat)
  | connected (table : Table width) (nextHandle : Nat) (cursors : List (Nat × Cursor width))
  | closed

namespace Connection

/-- Register one immutable module for this connection. -/
def register {width : Nat} (implementation : Module width) : Connection width :=
  .registered implementation 0

def xConnect {width : Nat} (conn : Connection width) (snapshot : Snapshot width) :
    Except Error (Connection width) :=
  match conn with
  | .registered implementation next => .ok (.connected ⟨implementation, snapshot⟩ next [])
  | .connected .. => .error .tableAlreadyConnected
  | .closed => .error .notRegistered

def xDisconnect {width : Nat} (conn : Connection width) : Except Error (Connection width) :=
  match conn with
  | .connected table next [] => .ok (.registered table.implementation next)
  | .connected .. => .error .cursorsOpen
  | _ => .error .tableDisconnected

/-- Close after retiring any connected table. -/
def close {width : Nat} (conn : Connection width) : Except Error (Connection width) :=
  match conn with
  | .registered .. => .ok .closed
  | .connected .. => conn.xDisconnect.map fun _ => .closed
  | .closed => .error .notRegistered

def xBestIndex {width : Nat} (conn : Connection width) (input : BestIndexInput width) :
    Except Error Plan :=
  match conn with
  | .connected table .. => table.xBestIndex input
  | _ => .error .tableDisconnected

def xOpen {width : Nat} (conn : Connection width) : Except Error (Connection width × Nat) :=
  match conn with
  | .connected table next cursors =>
    .ok (.connected table (next + 1) ((next, table.xOpen) :: cursors), next)
  | _ => .error .tableDisconnected

def cursor {width : Nat} (conn : Connection width) (handle : Nat) : Except Error (Cursor width) :=
  match conn with
  | .connected _ _ cursors =>
    match cursors.lookup handle with
    | some active => .ok active
    | none => .error .unknownCursor
  | _ => .error .tableDisconnected

def xClose {width : Nat} (conn : Connection width) (handle : Nat) :
    Except Error (Connection width) :=
  match conn with
  | .connected table next cursors => do
    let active ← conn.cursor handle
    let _ ← active.xClose
    return .connected table next (cursors.filter fun entry => entry.1 != handle)
  | _ => .error .tableDisconnected

def replaceCursor {width : Nat} (cursors : List (Nat × Cursor width)) (handle : Nat)
    (cursor : Cursor width) : List (Nat × Cursor width) :=
  cursors.map fun entry => if entry.1 == handle then (handle, cursor) else entry

/-- On a scan error, retain the failed cursor in the connection so it can
be closed or refiltered. -/
def xFilter {width : Nat} (conn : Connection width) (handle : Nat) (key : IndexKey)
    (argv : List Int64) : Connection width × Except Error Unit :=
  match conn with
  | .connected table next cursors =>
    match conn.cursor handle with
    | .error err => (conn, .error err)
    | .ok active =>
      let (cursor, status) := active.xFilter table key argv
      (.connected table next (replaceCursor cursors handle cursor), status)
  | _ => (conn, .error .tableDisconnected)

def xNext {width : Nat} (conn : Connection width) (handle : Nat) :
    Except Error (Connection width) :=
  match conn with
  | .connected table next cursors => do
    let active ← conn.cursor handle
    let cursor ← active.xNext
    return .connected table next (replaceCursor cursors handle cursor)
  | _ => .error .tableDisconnected

def xEof {width : Nat} (conn : Connection width) (handle : Nat) : Except Error Bool :=
  (conn.cursor handle).map Cursor.xEof

def xColumn {width : Nat} (conn : Connection width) (handle column : Nat) : Except Error Int64 :=
  (conn.cursor handle).bind (·.xColumn column)

def xRowid {width : Nat} (conn : Connection width) (handle : Nat) : Except Error Int64 :=
  (conn.cursor handle).bind Cursor.xRowid

end Connection
end Silmaril.Formats.Sqlite.VirtualTable
