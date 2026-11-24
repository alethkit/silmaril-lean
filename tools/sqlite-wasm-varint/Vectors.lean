module

public meta import Lean.Data.Json
public meta import Silmaril.Formats.Sqlite.Varint.Defs

meta section
open Lean Silmaril.Formats Silmaril.Formats.Sqlite

private def encodeCase (value : Nat) : Json :=
  let bytes := Varint.encode (UInt64.ofNat value)
  Json.mkObj [("value", toJson (toString value)), ("bytes", toJson (bytes.toList.map UInt8.toNat))]

private def decodeCase (bytes : Bytes) : IO Json := do
  let some (value, width) := Varint.read? (File.View.ofBytes bytes) 0
    | throw (IO.userError "incomplete decoder test input")
  pure <| Json.mkObj [
    ("bytes", toJson (bytes.toList.map UInt8.toNat)), ("value", toJson (toString value.toNat)),
    ("width", toJson width)]

public def main : IO Unit := do
  let octets := List.range 256
  let edges := (List.range 8).flatMap fun i =>
    let limit : Nat := 2 ^ (7 * (i + 1))
    [limit - 1, limit, limit + 1]
  let values := (octets ++ edges ++ [2^63 - 1, 2^63, 2^64 - 1] ++
    octets.map (2^56 + ·)).eraseDups
  let canonical := values.map (fun n => Varint.encode (UInt64.ofNat n))
  let overlong := (List.range 7).map fun i =>
    Bytes.ofList (List.replicate (i + 1) 0x80 ++ [0])
  let ninth := octets.map fun n => Bytes.ofList (List.replicate 8 0x80 ++ [UInt8.ofNat n])
  for n in List.range 9 do
    let incomplete := File.View.ofBytes (Bytes.ofList (List.replicate n 0x80))
    unless (Varint.read? incomplete 0).isNone do
      throw (IO.userError s!"expected Lean to reject a truncated encoding of length {n}")
  let decodes ← (canonical ++ overlong ++ ninth).mapM decodeCase
  IO.println (Json.mkObj [("encode", toJson (values.map encodeCase)), ("decode", toJson decodes)]).compress
