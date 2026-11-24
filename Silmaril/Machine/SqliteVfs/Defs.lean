module

public import Init.Data.List.OfFn
public import Init.Data.Int.Order

@[expose] public section

namespace Silmaril.Machine.SqliteVfs

abbrev Bytes := List UInt8

inductive Mode where
  | readOnly
  | readWrite
  deriving DecidableEq, Repr

/-- An abstract open-file handle. Tokens are scoped to one backing instance. -/
structure Handle where
  generation : Nat
  deriving DecidableEq, Repr

/-- Operations on one configured, already-existing file. Opening requests an exact mode. -/
inductive Request where
  | openFile (mode : Mode)
  | close (handle : Handle)
  | read (handle : Handle) (offset count : Int)
  | fileSize (handle : Handle)
  | write (handle : Handle) (offset : Int) (data : Bytes)
  | truncate (handle : Handle) (size : Int)
  deriving DecidableEq, Repr

/-- Failures in the selected abstract profile. The last two describe faults a
handler may report outside the concrete in-memory profile. -/
inductive Error where
  | cannotOpen
  | invalidHandle
  | invalidRange
  | readOnly
  | full
  | ioRead
  | ioWrite
  deriving DecidableEq, Repr

/-- Both successful and short reads expose a caller buffer. Other errors have
no buffer observation in this model. -/
inductive ReadReply where
  | ok (buffer : Bytes)
  | shortRead (buffer : Bytes)
  | error (reason : Error)
  deriving DecidableEq, Repr

def Response : Request → Type
  | .openFile _ => Except Error Handle
  | .read .. => ReadReply
  | .fileSize _ => Except Error Nat
  | .close _ | .write .. | .truncate .. => Except Error Unit

/-- Total dispatch with request-dependent results. The byte and handle laws
below can be imposed on a handler independently of its type. -/
abbrev Handler (State : Type) := State → (request : Request) → Response request × State

structure Exchange where
  request : Request
  response : Response request

abbrev Trace := List Exchange

/-- A trace records completed calls and their actual responses, including errors. -/
inductive Trace.Valid {State : Type} (step : Handler State) : State → Trace → State → Prop where
  | nil (state) : Valid step state [] state
  | cons {before middle after : State} {request : Request} {response : Response request}
      {rest : Trace} :
      step before request = (response, middle) →
      Valid step middle rest after →
      Valid step before (⟨request, response⟩ :: rest) after

def maxOffset : Nat := 2^63 - 1
def maxCount : Nat := 2^31 - 1

/-- Selected C-boundary admission. All endpoint arithmetic is mathematical. -/
def ReadRange (offset count : Int) : Prop :=
  0 ≤ offset ∧ 0 < count ∧ count ≤ Int.ofNat maxCount ∧ offset + count ≤ Int.ofNat maxOffset

def WriteRange (offset : Int) (count : Nat) : Prop :=
  ReadRange offset (Int.ofNat count)

def TruncateRange (size : Int) : Prop :=
  0 ≤ size ∧ size ≤ Int.ofNat maxOffset

instance (offset count : Int) : Decidable (ReadRange offset count) := by
  unfold ReadRange
  infer_instance

instance (offset : Int) (count : Nat) : Decidable (WriteRange offset count) :=
  inferInstanceAs (Decidable (ReadRange offset (Int.ofNat count)))

instance (size : Int) : Decidable (TruncateRange size) := by
  unfold TruncateRange
  infer_instance

/-- One file with at most one open handle. Closing advances the generation. -/
structure FileState where
  bytes : Bytes
  openMode : Option Mode := none
  generation : Nat := 0
  deriving DecidableEq, Repr

def FileState.mode (state : FileState) (handle : Handle) : Option Mode :=
  if handle.generation = state.generation then state.openMode else none

/-- In-memory capacity and the signed file-size representation both bound file data. -/
def WithinBounds (capacity : Nat) (state : FileState) : Prop :=
  state.bytes.length ≤ min capacity maxOffset

/-- Full or short success against a stable byte snapshot, including every buffer byte. -/
def ReadResult (bytes : Bytes) (offset count : Nat) (reply : ReadReply) : Prop :=
  ∃ buffer,
    reply = (if offset + count ≤ bytes.length then .ok buffer else .shortRead buffer) ∧
    buffer.length = count ∧
    ∀ i, i < count → buffer[i]? = some (bytes[offset + i]?.getD 0)

/-- The EOF zero-fill obligation for the stable-snapshot profile. This predicate
only constrains replies that report a short read. -/
def ShortReadZeroFill {State : Type} (step : Handler State) (view : State → FileState) : Prop :=
  ∀ state handle offset count buffer,
    (step state (.read handle offset count)).1 = .shortRead buffer →
    buffer.length = count.toNat ∧
    ∀ i, i < count.toNat → (view state).bytes.length ≤ offset.toNat + i →
      buffer[i]? = some 0

/-- Read and size laws on the observable state, including the selected rejection behavior. -/
structure ReadLaw {State : Type} (step : Handler State) (view : State → FileState) : Prop where
  read (state handle offset count) :
    let before := view state
    let (reply, after) := step state (.read handle offset count)
    view after = before ∧
      if (before.mode handle).isNone then reply = .error .invalidHandle
      else if ReadRange offset count then ReadResult before.bytes offset.toNat count.toNat reply
      else reply = .error .invalidRange
  fileSize (state handle) :
    let before := view state
    let (reply, after) := step state (.fileSize handle)
    view after = before ∧
      reply = if (before.mode handle).isNone then .error .invalidHandle else .ok before.bytes.length

/-- Opening an idle file installs one fresh token. Failed opens and invalid
closes preserve the view. A successful close retires its token. -/
structure HandleLaw {State : Type} (maximumMode : Mode) (step : Handler State)
    (view : State → FileState) : Prop where
  openFile (state requested) :
    let before := view state
    let (reply, after) := step state (.openFile requested)
    if before.openMode.isSome ∨ (maximumMode = .readOnly ∧ requested = .readWrite) then
      reply = .error .cannotOpen ∧ view after = before
    else
      reply = .ok ⟨before.generation⟩ ∧ view after = { before with openMode := some requested }
  close (state handle) :
    let before := view state
    let (reply, after) := step state (.close handle)
    if (before.mode handle).isNone then
      reply = .error .invalidHandle ∧ view after = before
    else
      reply = .ok () ∧
        view after = { before with openMode := none, generation := before.generation + 1 }

/-- Read-only backing rejects mutation even when the request has a live handle. -/
structure ReadOnlyLaw {State : Type} (step : Handler State) (view : State → FileState) : Prop where
  write (state handle offset data) :
    let before := view state
    let (reply, after) := step state (.write handle offset data)
    view after = before ∧
      reply = if (before.mode handle).isNone then .error .invalidHandle else .error .readOnly
  truncate (state handle size) :
    let before := view state
    let (reply, after) := step state (.truncate handle size)
    view after = before ∧
      reply = if (before.mode handle).isNone then .error .invalidHandle else .error .readOnly

/-- Overwrite the given interval, preserving the old prefix and suffix and
zero-filling any gap between the old EOF and the write offset. -/
def overwrite (bytes : Bytes) (offset : Nat) (data : Bytes) : Bytes :=
  bytes.take offset ++ List.replicate (offset - bytes.length) 0 ++
    data ++ bytes.drop (offset + data.length)

/-- Keep the prefix up to the requested length and zero-fill an extension. -/
def resize (bytes : Bytes) (size : Nat) : Bytes :=
  bytes.take size ++ List.replicate (size - bytes.length) 0

/-- The bounded mutation contract for a read-write backing. Every rejected
mutation preserves the observable state. The mode of each handle still applies. -/
structure BoundedWriteLaw {State : Type} (capacity : Nat) (step : Handler State)
    (view : State → FileState) : Prop where
  write (state handle offset data) :
    let before := view state
    let (reply, after) := step state (.write handle offset data)
    match before.mode handle with
    | none => reply = .error .invalidHandle ∧ view after = before
    | some .readOnly => reply = .error .readOnly ∧ view after = before
    | some .readWrite =>
      if WriteRange offset data.length then
        if offset.toNat + data.length ≤ capacity then
          reply = .ok () ∧ view after = { before with bytes := overwrite before.bytes offset.toNat data }
        else reply = .error .full ∧ view after = before
      else reply = .error .invalidRange ∧ view after = before
  truncate (state handle size) :
    let before := view state
    let (reply, after) := step state (.truncate handle size)
    match before.mode handle with
    | none => reply = .error .invalidHandle ∧ view after = before
    | some .readOnly => reply = .error .readOnly ∧ view after = before
    | some .readWrite =>
      if TruncateRange size then
        if size.toNat ≤ capacity then
          reply = .ok () ∧ view after = { before with bytes := resize before.bytes size.toNat }
        else reply = .error .full ∧ view after = before
      else reply = .error .invalidRange ∧ view after = before

def ReadOnlyProfile {State : Type} (step : Handler State) (view : State → FileState) : Prop :=
  HandleLaw .readOnly step view ∧ ReadLaw step view ∧ ReadOnlyLaw step view

def ReadWriteProfile {State : Type} (capacity : Nat) (step : Handler State)
    (view : State → FileState) : Prop :=
  HandleLaw .readWrite step view ∧ ReadLaw step view ∧ BoundedWriteLaw capacity step view

/-- A count-sized buffer, padded with zeros beyond EOF. -/
def readBytes (bytes : Bytes) (offset count : Nat) : Bytes :=
  List.ofFn fun i : Fin count => bytes[offset + i.val]?.getD 0

/-- The result of reading a finite byte snapshot. -/
def readBacking (bytes : Bytes) (offset count : Nat) : ReadReply :=
  let buffer := readBytes bytes offset count
  if offset + count ≤ bytes.length then .ok buffer else .shortRead buffer

/-- A deterministic bounded file in memory. The capacity concerns file
contents. Initial data must fit it to start with a bounded backing. -/
def backing (maximumMode : Mode) (capacity : Nat) : Handler FileState :=
  fun state request => match request with
  | .openFile requested =>
    if state.openMode.isSome ∨ (maximumMode = .readOnly ∧ requested = .readWrite) then
      (.error .cannotOpen, state)
    else (.ok ⟨state.generation⟩, { state with openMode := some requested })
  | .close handle =>
    if (state.mode handle).isNone then (.error .invalidHandle, state)
    else (.ok (), { state with openMode := none, generation := state.generation + 1 })
  | .read handle offset count =>
    if (state.mode handle).isNone then (.error .invalidHandle, state)
    else if ReadRange offset count then (readBacking state.bytes offset.toNat count.toNat, state)
    else (.error .invalidRange, state)
  | .fileSize handle =>
    if (state.mode handle).isNone then (.error .invalidHandle, state) else (.ok state.bytes.length, state)
  | .write handle offset data =>
    match state.mode handle with
    | none => (.error .invalidHandle, state)
    | some mode =>
      if maximumMode = .readOnly ∨ mode = .readOnly then (.error .readOnly, state)
      else if WriteRange offset data.length then
        if offset.toNat + data.length ≤ capacity then
          (.ok (), { state with bytes := overwrite state.bytes offset.toNat data })
        else (.error .full, state)
      else (.error .invalidRange, state)
  | .truncate handle size =>
    match state.mode handle with
    | none => (.error .invalidHandle, state)
    | some mode =>
      if maximumMode = .readOnly ∨ mode = .readOnly then (.error .readOnly, state)
      else if TruncateRange size then
        if size.toNat ≤ capacity then (.ok (), { state with bytes := resize state.bytes size.toNat })
        else (.error .full, state)
      else (.error .invalidRange, state)

abbrev readOnly (capacity : Nat) : Handler FileState := backing .readOnly capacity
abbrev readWrite (capacity : Nat) : Handler FileState := backing .readWrite capacity

/-- Fills the unread suffix of a short read with nonzero bytes. -/
def badShortRead (capacity : Nat) : Handler FileState :=
  fun state request => match request with
  | .read handle offset count =>
    match readOnly capacity state (.read handle offset count) with
    | (.shortRead buffer, after) =>
      let available := state.bytes.length - offset.toNat
      let corrupted := buffer.take available ++ (buffer.drop available).map (fun _ => 255)
      (.shortRead corrupted, after)
    | result => result
  | .openFile mode => readOnly capacity state (.openFile mode)
  | .close handle => readOnly capacity state (.close handle)
  | .fileSize handle => readOnly capacity state (.fileSize handle)
  | .write handle offset data => readOnly capacity state (.write handle offset data)
  | .truncate handle size => readOnly capacity state (.truncate handle size)

end Silmaril.Machine.SqliteVfs
