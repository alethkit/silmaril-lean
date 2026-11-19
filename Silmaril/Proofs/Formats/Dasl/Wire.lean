module

public import Silmaril.Formats.Dasl.Wire.Defs
import Silmaril.Formats.Cbor.Drisl.Number.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl

open Silmaril.Formats.Cbor

theorem i64_roundtrip (bits : UInt64) :
    (Drisl.i64Cbor.readNumber? (Drisl.i64Cbor.number bits.toInt64)).map Int64.toUInt64 = some bits := by
  have signed : Drisl.i64Cbor.readNumber? (Drisl.i64Cbor.number bits.toInt64) = some bits.toInt64 := by
    have parsed := Drisl.int64_toInt bits.toInt64
    cases view : bits.toInt64.toInt <;> simpa [Drisl.i64Cbor, view] using parsed
  simp [signed]

end Silmaril.Proofs.Formats.Dasl
