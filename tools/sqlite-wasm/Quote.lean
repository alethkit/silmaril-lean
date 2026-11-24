module

public import Silmaril.Wasm.Binary.Quote.Defs

public meta section

namespace SqliteWasm

open Lean Elab Command Silmaril Silmaril.Wasm

/-- Create an executable declaration from the same explicit Core term as the generic
quotation command. The fixture's body groups bound the compilation workload. -/
elab "sqlite_wasm_part " name:ident " from " file:str : command => do
  let ns ← getCurrNamespace
  liftCoreM <| withRef file do
    let start ← IO.monoMsNow
    let bytes ← KBytes.Elab.readRelative file.getString
    let decoded ← ofExcept (Binary.Core.Decode.decodeModule bytes)
    let decodedAt ← IO.monoMsNow
    let term := Binary.Quote.quoteModule decoded
    let quotedAt ← IO.monoMsNow
    withOptions (Elab.async.set · false) do
      KBytes.Elab.addDefn (ns ++ name.getId) (mkConst ``Wasm.Module) term true
    let compiledAt ← IO.monoMsNow
    logInfo m!"{file.getString}: read/decode {decodedAt - start} ms, quotation {quotedAt - decodedAt} ms, declaration {compiledAt - quotedAt} ms"

end SqliteWasm
