module

public import Silmaril.Machine.SqliteVfs.Defs
import Silmaril.Proofs.Machine.SqliteVfs.Backing

@[expose] public section

namespace Silmaril.Machine.SqliteVfs

theorem zeroFill_of_readLaw {State : Type} {step : Handler State} {view : State → FileState}
    (law : ReadLaw step view) : ShortReadZeroFill step view :=
  Proofs.Machine.SqliteVfs.zeroFill_of_readLaw law

theorem readOnly_lawful (capacity : Nat) : ReadOnlyProfile (readOnly capacity) id :=
  ⟨Proofs.Machine.SqliteVfs.handleLaw_backing _ _, Proofs.Machine.SqliteVfs.readLaw_backing _ _,
    Proofs.Machine.SqliteVfs.readOnlyLaw_backing _⟩

theorem readWrite_lawful (capacity : Nat) : ReadWriteProfile capacity (readWrite capacity) id :=
  ⟨Proofs.Machine.SqliteVfs.handleLaw_backing _ _, Proofs.Machine.SqliteVfs.readLaw_backing _ _,
    Proofs.Machine.SqliteVfs.boundedWriteLaw_backing _⟩

theorem overwrite_length (bytes : Bytes) (offset : Nat) (data : Bytes) :
    (overwrite bytes offset data).length = max bytes.length (offset + data.length) :=
  Proofs.Machine.SqliteVfs.overwrite_length bytes offset data

theorem resize_length (bytes : Bytes) (size : Nat) : (resize bytes size).length = size :=
  Proofs.Machine.SqliteVfs.resize_length bytes size

theorem backing_trace_bounds {mode : Mode} {capacity : Nat} {start finish : FileState} {trace : Trace}
    (valid : Trace.Valid (backing mode capacity) start trace finish)
    (bounded : WithinBounds capacity start) : WithinBounds capacity finish :=
  Proofs.Machine.SqliteVfs.backing_trace_bounds valid bounded

/-- Every completed trace in the read-only profile preserves the file contents. -/
theorem readOnly_trace_bytes {State : Type} {step : Handler State} {view : State → FileState}
    (law : ReadOnlyProfile step view) {start finish : State} {trace : Trace}
    (valid : Trace.Valid step start trace finish) : (view finish).bytes = (view start).bytes :=
  Proofs.Machine.SqliteVfs.readOnly_trace_bytes law valid

theorem bad_preserves_readOnly (capacity : Nat) : ReadOnlyLaw (badShortRead capacity) id :=
  Proofs.Machine.SqliteVfs.bad_preserves_readOnly capacity

theorem bad_violates_zeroFill (capacity : Nat) : ¬ ShortReadZeroFill (badShortRead capacity) id :=
  Proofs.Machine.SqliteVfs.bad_violates_zeroFill capacity

theorem bad_not_readOnlyProfile (capacity : Nat) : ¬ ReadOnlyProfile (badShortRead capacity) id :=
  fun profile => bad_violates_zeroFill capacity (zeroFill_of_readLaw profile.2.1)

end Silmaril.Machine.SqliteVfs
