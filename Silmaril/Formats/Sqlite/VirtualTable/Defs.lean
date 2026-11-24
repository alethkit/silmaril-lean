module
public import Init.Data.List.Perm
public import Init.Data.List.Sort.Lemmas
public import Init.Data.Vector.Lemmas
public import Init.Data.SInt.Lemmas

/-! Read-only, rowid-bearing virtual tables over signed 64-bit integers.
The planner sees constraint metadata. Only the selected scan receives the
requested right-hand sides, after the caller has evaluated them. -/
@[expose] public section
namespace Silmaril.Formats.Sqlite.VirtualTable

structure Row (width : Nat) where
  rowid : Int64
  values : Vector Int64 width
  deriving DecidableEq, Repr

abbrev Relation (width : Nat) := List (Row width)

/-- One immutable view of the relation, with distinct rowids and an independent
storage order. -/
structure Snapshot (width : Nat) where
  rows : Relation width
  uniqueRowids : (rows.map Row.rowid).Nodup

inductive Column (width : Nat) where
  | rowid
  | value (index : Fin width)
  deriving DecidableEq, Repr

def Row.get {width : Nat} (row : Row width) : Column width → Int64
  | .rowid => row.rowid
  | .value i => row.values[i]

inductive Operator where
  | eq | lt | le | gt | ge
  deriving DecidableEq, Repr

def Operator.test (op : Operator) (lhs rhs : Int64) : Bool :=
  match op with
  | .eq => decide (lhs = rhs)
  | .lt => decide (lhs < rhs)
  | .le => decide (lhs ≤ rhs)
  | .gt => decide (rhs < lhs)
  | .ge => decide (rhs ≤ lhs)

structure Constraint (width : Nat) where
  column : Column width
  op : Operator
  usable : Bool
  deriving DecidableEq, Repr

/-- The order fragment is a single signed rowid key. -/
inductive Direction where
  | asc | desc
  deriving DecidableEq, Repr

def Direction.before {width : Nat} (dir : Direction) (a b : Row width) : Bool :=
  match dir with
  | .asc => decide (a.rowid ≤ b.rowid)
  | .desc => decide (b.rowid ≤ a.rowid)

def Direction.sort {width : Nat} (dir : Direction) (rows : Relation width) : Relation width :=
  rows.mergeSort dir.before

structure BestIndexInput (width : Nat) where
  constraints : List (Constraint width)
  orderBy : Option Direction
  deriving DecidableEq, Repr

structure IndexKey where
  idxNum : Int32
  idxStr : Option String := none
  deriving DecidableEq, Repr

structure Argument where
  constraint : Nat
  «omit» : Bool := false
  deriving DecidableEq, Repr

structure Plan where
  key : IndexKey
  /-- At list offset k, request argvIndex k+1 for this zero-based constraint.
  Constraints absent from this list have argvIndex=0 and omit=false. -/
  arguments : List Argument := []
  orderByConsumed : Bool := false
  deriving DecidableEq, Repr

def Plan.validLayout {width : Nat} (plan : Plan) (input : BestIndexInput width) : Bool :=
  decide ((plan.arguments.map Argument.constraint).Nodup) &&
    plan.arguments.zipIdx.all (fun (arg, i) =>
      (input.constraints[arg.constraint]?.any Constraint.usable) &&
        (!arg.omit || (i < 16 && arg.constraint < 16))) &&
    (!plan.orderByConsumed || input.orderBy.isSome)

inductive Error where
  /-- xBestIndex declines this combination of inputs (SQLITE_CONSTRAINT). -/
  | noPlan
  /-- An implementation-provided SQLite error status. -/
  | backend (code : Int32) (nonzero : code ≠ 0)
  | invalidPlan | unknownIndex | argumentCount | dishonestPlan
  | notRegistered | tableAlreadyConnected | tableDisconnected | cursorsOpen | unknownCursor
  | unfiltered | atEnd | cursorClosed | columnOutOfRange
  deriving DecidableEq, Repr

/-- A scan strategy selected by idxNum/idxStr. Its output is a candidate stream
that can include rows failing predicates left for the caller to recheck. -/
abbrev Index (width : Nat) := Snapshot width → List Int64 → Except Error (Relation width)

structure Module (width : Nat) where
  bestIndex : BestIndexInput width → Except Error Plan
  index : IndexKey → Option (Index width)

structure Table (width : Nat) where
  implementation : Module width
  snapshot : Snapshot width

def Table.xBestIndex {width : Nat} (table : Table width) (input : BestIndexInput width) :
    Except Error Plan := do
  let plan ← table.implementation.bestIndex input
  if !plan.validLayout input then throw .invalidPlan
  else if (table.implementation.index plan.key).isNone then throw .unknownIndex
  else return plan

def Table.scan {width : Nat} (table : Table width) (key : IndexKey) (argv : List Int64) :
    Except Error (Relation width) := do
  let some index := table.implementation.index key | throw .unknownIndex
  index table.snapshot argv

/-- The remaining rows of a successful scan. An empty suffix denotes EOF.
A failed xFilter invalidates the previous position but allows refilter/close. -/
inductive Cursor (width : Nat) where
  | unfiltered
  | scanning (remaining : Relation width)
  | failed (error : Error)
  | closed
  deriving DecidableEq, Repr

def Table.xOpen {width : Nat} (_table : Table width) : Cursor width := .unfiltered

def Cursor.xFilter {width : Nat} (cursor : Cursor width) (table : Table width)
    (key : IndexKey) (argv : List Int64) : Cursor width × Except Error Unit :=
  match cursor with
  | .closed => (.closed, .error .cursorClosed)
  | _ => match table.scan key argv with
    | .ok rows => (.scanning rows, .ok ())
    | .error err => (.failed err, .error err)

def Cursor.xEof {width : Nat} : Cursor width → Bool
  | .scanning (_ :: _) => false
  | _ => true

def Cursor.current {width : Nat} : Cursor width → Except Error (Row width)
  | .unfiltered => .error .unfiltered
  | .scanning [] => .error .atEnd
  | .scanning (row :: _) => .ok row
  | .failed err => .error err
  | .closed => .error .cursorClosed

def Cursor.xNext {width : Nat} (cursor : Cursor width) : Except Error (Cursor width) :=
  match cursor with
  | .scanning (_ :: rest) => .ok (.scanning rest)
  | .unfiltered => .error .unfiltered
  | .scanning [] => .error .atEnd
  | .failed err => .error err
  | .closed => .error .cursorClosed

def Cursor.xColumn {width : Nat} (cursor : Cursor width) (column : Nat) : Except Error Int64 := do
  let row ← cursor.current
  if h : column < width then return row.values[column]
  else throw .columnOutOfRange

def Cursor.xRowid {width : Nat} (cursor : Cursor width) : Except Error Int64 :=
  cursor.current.map Row.rowid

def Cursor.xClose {width : Nat} : Cursor width → Except Error (Cursor width)
  | .closed => .error .cursorClosed
  | _ => .ok .closed

/-- Successful observations of a positioned scan, including the final EOF.
The row observation represents all xColumn results together with xRowid. -/
inductive ScanTrace {width : Nat} : Cursor width → Relation width → Prop where
  | endOfScan : ScanTrace (.scanning []) []
  | step {cursor next : Cursor width} {row : Row width} {rows : Relation width}
      (atRow : cursor.xEof = false) (read : cursor.current = .ok row)
      (advance : cursor.xNext = .ok next) (rest : ScanTrace next rows) :
      ScanTrace cursor (row :: rows)

/-- Right-hand sides in constraint-array order, including terms unavailable at
xBestIndex time. This represents one scan after all reference predicates are
known to the caller. -/
structure Query (width : Nat) where
  input : BestIndexInput width
  rhs : Vector Int64 input.constraints.length

def Query.argv {width : Nat} (query : Query width) (plan : Plan) : Except Error (List Int64) :=
  plan.arguments.mapM fun arg =>
    match query.rhs.toArray[arg.constraint]? with
    | some value => .ok value
    | none => .error .invalidPlan

def Query.matches {width : Nat} (query : Query width) (keep : Nat → Bool)
    (row : Row width) : Bool :=
  (query.input.constraints.zip query.rhs.toList).zipIdx.all fun ((term, rhs), i) =>
    !keep i || term.op.test (row.get term.column) rhs

def Plan.omits (plan : Plan) (constraint : Nat) : Bool :=
  plan.arguments.any fun arg => arg.constraint == constraint && arg.omit

def Query.matchingRows {width : Nat} (query : Query width) (snapshot : Snapshot width) :
    Relation width :=
  snapshot.rows.filter (query.matches fun _ => true)

def Query.reference {width : Nat} (query : Query width) (snapshot : Snapshot width) :
    Relation width :=
  let matching := query.matchingRows snapshot
  match query.input.orderBy with
  | none => matching
  | some dir => dir.sort matching

/-- Skipping an omit hint conservatively just rechecks another term. This
function models the executor that trusts every omit hint in the profile. -/
def Query.finish {width : Nat} (query : Query width) (plan : Plan) (rows : Relation width) :
    Relation width :=
  let residual := rows.filter (query.matches fun i => !plan.omits i)
  match query.input.orderBy with
  | some dir => if plan.orderByConsumed then residual else dir.sort residual
  | none => residual

/-- Checkable obligations for one invocation of a proposed plan on a snapshot.
Coverage includes multiplicity. The ordering and omission promises are tested
on the raw scan, before residual predicates have removed any rows. -/
structure Honest {width : Nat} (query : Query width) (plan : Plan)
    (snapshot : Snapshot width) (rows : Relation width) : Prop where
  layout : plan.validLayout query.input = true
  fromSnapshot : ∀ row ∈ rows, row ∈ snapshot.rows
  uniqueScan : (rows.map Row.rowid).Nodup
  covers : (rows.filter (query.matches fun _ => true)).Perm (query.matchingRows snapshot)
  omits : ∀ row ∈ rows, query.matches plan.omits row = true
  order : plan.orderByConsumed = true → ∀ dir, query.input.orderBy = some dir →
    rows.Pairwise (fun a b => dir.before a b = true)

/-- Finite check of the same obligations, useful for rejecting proposed claims.
This is an audit of a concrete invocation, separate from xBestIndex itself. -/
def checkHonesty {width : Nat} (query : Query width) (plan : Plan)
    (snapshot : Snapshot width) (rows : Relation width) : Bool :=
  plan.validLayout query.input &&
    rows.all (fun row => decide (row ∈ snapshot.rows)) &&
    decide ((rows.map Row.rowid).Nodup) &&
    decide ((rows.filter (query.matches fun _ => true)).Perm (query.matchingRows snapshot)) &&
    rows.all (query.matches plan.omits) &&
    (!plan.orderByConsumed ||
      query.input.orderBy.any fun dir => decide (rows.Pairwise (fun a b => dir.before a b = true)))

def Cursor.scanRows {width : Nat} (cursor : Cursor width) : Except Error (Relation width) :=
  match cursor with
  | .scanning rows => .ok rows
  | .unfiltered => .error .unfiltered
  | .failed err => .error err
  | .closed => .error .cursorClosed

def Table.startQuery {width : Nat} (table : Table width) (query : Query width) :
    Except Error (Plan × Cursor width) := do
  let plan ← table.xBestIndex query.input
  let argv ← query.argv plan
  let (cursor, status) := table.xOpen.xFilter table plan.key argv
  status
  return (plan, cursor)

/-- Execute the selected scan and apply the predicates and ordering left to
the caller. Use the plan obligations to justify trusting its claims. -/
def Table.run {width : Nat} (table : Table width) (query : Query width) :
    Except Error (Relation width) := do
  let (plan, cursor) ← table.startQuery query
  return query.finish plan (← cursor.scanRows)

/-- A finite audit runner. The returned rows are the reference query's
observation under the plan, with residual checking and sorting as needed. -/
def Table.runChecked {width : Nat} (table : Table width) (query : Query width) :
    Except Error (Relation width) := do
  let (plan, cursor) ← table.startQuery query
  let rows ← cursor.scanRows
  if checkHonesty query plan table.snapshot rows then return query.finish plan rows
  else throw .dishonestPlan

end Silmaril.Formats.Sqlite.VirtualTable
