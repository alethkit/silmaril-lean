module

public import Silmaril.Machine.SqliteVfs.Defs
import Init.Omega

public section

namespace Silmaril.Proofs.Machine.SqliteVfs

open Silmaril.Machine.SqliteVfs

theorem readBacking_result (bytes : Bytes) (offset count : Nat) :
    ReadResult bytes offset count (readBacking bytes offset count) := by
  refine ⟨readBytes bytes offset count, rfl, by simp [readBytes], ?_⟩
  intro i bound
  simp [readBytes, bound]

theorem readLaw_backing (mode : Mode) (capacity : Nat) : ReadLaw (backing mode capacity) id := by
  constructor
  · intro state handle offset count
    by_cases live : (state.mode handle).isNone
    · simp [Response, backing, live]
    · by_cases valid : ReadRange offset count
      · simpa [backing, live, valid] using readBacking_result state.bytes offset.toNat count.toNat
      · simp [Response, backing, live, valid]
  · intro state handle
    by_cases live : (state.mode handle).isNone <;> simp [Response, backing, live]

theorem zeroFill_of_readLaw {State : Type} {step : Handler State} {view : State → FileState}
    (law : ReadLaw step view) : ShortReadZeroFill step view := by
  intro state handle offset count buffer short
  have result := (law.read state handle offset count).2
  rw [short] at result
  split at result
  · cases result
  split at result
  · obtain ⟨expected, status, length, bytes⟩ := result
    split at status
    · cases status
    · cases status
      refine ⟨length, fun i within pastEOF => ?_⟩
      have absent : (view state).bytes[offset.toNat + i]? = none :=
        List.getElem?_eq_none_iff.mpr pastEOF
      simpa [absent] using bytes i within
  · cases result

theorem handleLaw_backing (mode : Mode) (capacity : Nat) : HandleLaw mode (backing mode capacity) id := by
  constructor
  · intro state requested
    by_cases blocked : state.openMode.isSome ∨ (mode = .readOnly ∧ requested = .readWrite) <;>
      simp [Response, backing, blocked]
  · intro state handle
    by_cases live : (state.mode handle).isNone <;> simp [Response, backing, live]

theorem readOnlyLaw_backing (capacity : Nat) : ReadOnlyLaw (readOnly capacity) id := by
  constructor
  · intro state handle offset data
    cases live : state.mode handle <;> simp [Response, backing, live]
  · intro state handle size
    cases live : state.mode handle <;> simp [Response, backing, live]

theorem boundedWriteLaw_backing (capacity : Nat) : BoundedWriteLaw capacity (readWrite capacity) id := by
  constructor
  · intro state handle offset data
    cases live : state.mode handle with
    | none => simp [Response, backing, live]
    | some mode =>
      cases mode
      · simp [Response, backing, live]
      · by_cases range : WriteRange offset data.length <;>
          by_cases fits : offset.toNat + data.length ≤ capacity <;> simp [Response, backing, live, range, fits]
  · intro state handle size
    cases live : state.mode handle with
    | none => simp [Response, backing, live]
    | some mode =>
      cases mode
      · simp [Response, backing, live]
      · by_cases range : TruncateRange size <;>
          by_cases fits : size.toNat ≤ capacity <;> simp [Response, backing, live, range, fits]

theorem overwrite_length (bytes : Bytes) (offset : Nat) (data : Bytes) :
    (overwrite bytes offset data).length = max bytes.length (offset + data.length) := by
  simp only [overwrite, List.length_append, List.length_take, List.length_replicate, List.length_drop]
  omega

theorem resize_length (bytes : Bytes) (size : Nat) : (resize bytes size).length = size := by
  simp only [resize, List.length_append, List.length_take, List.length_replicate]
  omega

theorem backing_preserves_bounds (mode : Mode) (capacity : Nat) (state : FileState) (request : Request)
    (bounded : WithinBounds capacity state) :
    WithinBounds capacity (backing mode capacity state request).2 := by
  cases request with
  | openFile requested =>
    simp only [backing]
    split <;> exact bounded
  | close handle =>
    simp only [backing]
    split <;> exact bounded
  | read handle offset count =>
    simp only [backing]
    split
    · exact bounded
    split <;> exact bounded
  | fileSize handle =>
    simp only [backing]
    split <;> exact bounded
  | write handle offset data =>
    simp only [backing]
    split
    · exact bounded
    split
    · exact bounded
    split
    · next range =>
      split
      · next fits =>
        have limit : offset.toNat + data.length ≤ maxOffset := by
          rcases range with ⟨nonnegative, _, _, upper⟩
          change offset + (data.length : Int) ≤ (maxOffset : Int) at upper
          omega
        simp only [WithinBounds, overwrite_length] at bounded ⊢
        omega
      · exact bounded
    · exact bounded
  | truncate handle size =>
    simp only [backing]
    split
    · exact bounded
    split
    · exact bounded
    split
    · next range =>
      split
      · next fits =>
        have limit : size.toNat ≤ maxOffset := by
          rcases range with ⟨nonnegative, upper⟩
          change size ≤ (maxOffset : Int) at upper
          omega
        simp only [WithinBounds, resize_length]
        omega
      · exact bounded
    · exact bounded

theorem backing_trace_bounds {mode : Mode} {capacity : Nat} {start finish : FileState} {trace : Trace}
    (valid : Trace.Valid (backing mode capacity) start trace finish)
    (bounded : WithinBounds capacity start) : WithinBounds capacity finish := by
  induction valid with
  | nil => exact bounded
  | @cons before middle after request response rest step _ advance =>
    apply advance
    have successor := backing_preserves_bounds mode capacity before request bounded
    rwa [step] at successor

private theorem readOnly_step_bytes {State : Type} {step : Handler State} {view : State → FileState}
    (law : ReadOnlyProfile step view) (state : State) (request : Request) :
    (view (step state request).2).bytes = (view state).bytes := by
  cases request with
  | openFile mode =>
    have opens := law.1.openFile state mode
    dsimp only at opens
    split at opens <;> simpa only using congrArg FileState.bytes opens.2
  | close handle =>
    have closes := law.1.close state handle
    dsimp only at closes
    split at closes <;> simpa only using congrArg FileState.bytes closes.2
  | read handle offset count =>
    exact congrArg FileState.bytes (law.2.1.read state handle offset count).1
  | fileSize handle =>
    exact congrArg FileState.bytes (law.2.1.fileSize state handle).1
  | write handle offset data =>
    exact congrArg FileState.bytes (law.2.2.write state handle offset data).1
  | truncate handle size =>
    exact congrArg FileState.bytes (law.2.2.truncate state handle size).1

theorem readOnly_trace_bytes {State : Type} {step : Handler State} {view : State → FileState}
    (law : ReadOnlyProfile step view) {start finish : State} {trace : Trace}
    (valid : Trace.Valid step start trace finish) : (view finish).bytes = (view start).bytes := by
  induction valid with
  | nil => rfl
  | @cons before middle after request response rest next _ same =>
    have first := readOnly_step_bytes law before request
    rw [next] at first
    exact same.trans first

theorem bad_preserves_readOnly (capacity : Nat) : ReadOnlyLaw (badShortRead capacity) id :=
  ⟨(readOnlyLaw_backing capacity).write, (readOnlyLaw_backing capacity).truncate⟩

theorem bad_violates_zeroFill (capacity : Nat) : ¬ ShortReadZeroFill (badShortRead capacity) id := by
  intro law
  let state : FileState := ⟨[], some .readOnly, 0⟩
  have bad := (law state ⟨0⟩ 0 1 [255] rfl).2 0 (by decide) (by decide)
  change some (255 : UInt8) = some 0 at bad
  nomatch bad

end Silmaril.Proofs.Machine.SqliteVfs
