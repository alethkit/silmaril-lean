module

public import Silmaril.Formats.Sqlite.Vdbe.Defs

/-! A single logical table shaped like
`CREATE TABLE sample(id INTEGER PRIMARY KEY, amount INTEGER NOT NULL) STRICT`.
The profile admits explicit integer rowids and integer or NULL payload literals.
NULL payloads exercise the constraint. The state contains no file or pager. -/
@[expose] public section
namespace Silmaril.Formats.Sqlite.WriteProfile

structure Row where
  id : Int64
  amount : Int64

def Row.entry (row : Row) : Int × List Value :=
  (row.id.toInt, [.integer row.id, .integer row.amount])

structure Snapshot where
  rows : List Row
  unique : (rows.map Row.id).Nodup

def Snapshot.empty : Snapshot := ⟨[], .nil⟩

def Snapshot.has (snapshot : Snapshot) (key : Int64) : Prop :=
  key ∈ snapshot.rows.map Row.id

instance (snapshot : Snapshot) (key : Int64) : Decidable (snapshot.has key) :=
  inferInstanceAs (Decidable (key ∈ snapshot.rows.map Row.id))

def Snapshot.orderedRows (snapshot : Snapshot) : List Row :=
  snapshot.rows.mergeSort fun a b => decide (a.id.toInt ≤ b.id.toInt)

/-- A rowid-ordered VM view. Logical edits may keep rows in insertion order. -/
def Snapshot.readTable (snapshot : Snapshot) : Vdbe.Table :=
  BTree.Query.ReadModel.ofList (snapshot.orderedRows.map Row.entry)

inductive Error where
  | rowidType
  | amountType
  | notNull
  | duplicateRowid
  | transactionActive
  | noTransaction
  deriving DecidableEq, BEq, Repr

inductive Edit where
  | insert (id amount : Value)
  | update (id amount : Value)
  | delete (id : Value)

def decodeRowid : Value → Except Error Int64
  | .integer id => .ok id
  | _ => .error .rowidType

def decodeAmount : Value → Except Error (Option Int64)
  | .integer amount => .ok (some amount)
  | .null => .ok none
  | _ => .error .amountType

def requireAmount : Option Int64 → Except Error Int64
  | some amount => .ok amount
  | none => .error .notNull

def replace (id amount : Int64) (row : Row) : Row :=
  if row.id = id then { row with amount := amount } else row

@[simp] theorem replace_id (id amount : Int64) (row : Row) :
    (replace id amount row).id = row.id := by
  simp only [replace]; split <;> rfl

structure Edited where
  snapshot : Snapshot
  changed : Nat

/-- Insertion preserves all old rows and rejects a duplicate identity. -/
def Snapshot.insert (snapshot : Snapshot) (id value : Int64) : Except Error Edited :=
  if fresh : ¬ snapshot.has id then
    let rows : List Row := ⟨id, value⟩ :: snapshot.rows
    .ok ⟨⟨rows, List.nodup_cons.mpr ⟨fresh, snapshot.unique⟩⟩, 1⟩
  else
    .error .duplicateRowid

/-- Updating an absent identity succeeds with zero changes. NULL is rejected
when the matching row would be updated. -/
def Snapshot.update (snapshot : Snapshot) (id : Int64) (value : Option Int64) :
    Except Error Edited :=
  if snapshot.has id then
    match value with
    | none => .error .notNull
    | some value =>
      let rows := snapshot.rows.map (replace id value)
      have unique : (rows.map Row.id).Nodup := by
        simpa [rows, List.map_map, Function.comp_def] using snapshot.unique
      .ok ⟨⟨rows, unique⟩, 1⟩
  else
    .ok ⟨snapshot, 0⟩

def Snapshot.erase (snapshot : Snapshot) (id : Int64) : Edited :=
  let rows := snapshot.rows.filter (fun row => row.id != id)
  let unique := List.Nodup.sublist (List.Sublist.map Row.id List.filter_sublist) snapshot.unique
  ⟨⟨rows, unique⟩, if snapshot.has id then 1 else 0⟩

/-- Admit the literal storage classes before executing the logical edit. -/
def Snapshot.apply (snapshot : Snapshot) : Edit → Except Error Edited
  | .insert id value => do
    let key ← decodeRowid id
    snapshot.insert key (← requireAmount (← decodeAmount value))
  | .update id value => do
    let key ← decodeRowid id
    snapshot.update key (← decodeAmount value)
  | .delete id => return snapshot.erase (← decodeRowid id)

structure State where
  committed : Snapshot
  pending : Option Snapshot := none

def State.empty : State := ⟨.empty, none⟩

def State.visible (state : State) : Snapshot :=
  state.pending.getD state.committed

/-- The sole table is exposed to the read-only VM at database 0, root 2.
These are logical identifiers. -/
def State.readDatabase (state : State) : Vdbe.Database :=
  fun database root => if database = 0 ∧ root = 2 then some state.visible.readTable else none

inductive Command where
  | edit (action : Edit)
  | begin
  | commit
  | rollback

inductive Success where
  | changed (count : Nat)
  | transaction
  deriving DecidableEq, BEq, Repr

structure Outcome where
  state : State
  result : Except Error Success

/-- Autocommit installs successful edits directly. Inside BEGIN they replace
the pending snapshot. A failed statement preserves both snapshots. -/
def step (state : State) : Command → Outcome
  | .edit edit =>
    match state.visible.apply edit with
    | .error error => ⟨state, .error error⟩
    | .ok edited =>
      let next := if state.pending.isSome then {state with pending := some edited.snapshot}
        else {state with committed := edited.snapshot}
      ⟨next, .ok (.changed edited.changed)⟩
  | .begin =>
    if state.pending.isSome then ⟨state, .error .transactionActive⟩
    else ⟨{state with pending := some state.committed}, .ok .transaction⟩
  | .commit =>
    match state.pending with
    | none => ⟨state, .error .noTransaction⟩
    | some pending => ⟨⟨pending, none⟩, .ok .transaction⟩
  | .rollback =>
    if state.pending.isSome then ⟨{state with pending := none}, .ok .transaction⟩
    else ⟨state, .error .noTransaction⟩

end Silmaril.Formats.Sqlite.WriteProfile
