module

public import Silmaril.Wasm.Component.InstTests.Defs
public import Silmaril.Wasm.Component.InstRef.Defs
public import Silmaril.Wasm.Component.Reference.Bridge.Defs

/-!
# Component test binaries on the reference machine

The reference machine (`Silmaril.Wasm.Component.Reference`) reads components in its own syntax,
`Core3Component`. There is no translation from component binaries into that syntax, so the two
test components are written here **by hand**, following `examples/component-tests/*.wat`
definition by definition, in the encoding of `SimpleI.toRef` (`SimpleI.importsDefs` for the
import, `SimpleI.exportsDefsAt` for the export). The core modules are the modules the core decoder
reads from the bytes embedded in the binaries (`Binary.coreModule call1CM`, …), so only the
component-level wiring is transcribed:

* `startsRef`: import `f: func(a: u32)`; core modules `call1`, `call2`, `glob`; `canon lower` of
  `f` (core function `0`); the core instance exporting it as `"f"` (core instance `0`); the
  instances of `call1` and `call2` with it as `"env"` (core instances `1`, `2`) and of `glob`
  (core instance `3`); `glob`'s `get`, aliased, `canon lift`ed and exported;
* `trapRef`: import `f`; core modules `trap`, `call2`; `canon lower` of `f`; its core instance;
  the instances of `trap` (core instance `1`) and of `call2` with `"env"` (core instance `2`);
  `trap`'s `get`, aliased, lifted and exported.

The reference host is the logging host `InstRef.embL` (every import call answered `()`, each call
appended to a log).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.InstTestsRef

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.InstLitmus Silmaril.Wasm.Component.InstTests

/-- The export `get: func() -> u32` of core export `0`. -/
def getSX : SimpleExport := ⟨"get", ⟨[], [.u32]⟩, 0⟩

/-- **`starts.wat` in the reference machine's syntax.** -/
def startsRef : Core3Component :=
  (SimpleI.importsDefs hostI 0).1 ++
  [.coreModule (Binary.coreModule call1CM), .coreModule (Binary.coreModule call2CM),
   .coreModule (Binary.coreModule globCM), .canon (.lower 0 []),
   .coreInstance (.exports [("f", ⟨.func, 0⟩)]), .coreInstance (.instantiate 0 [("env", 0)]),
   .coreInstance (.instantiate 1 [("env", 0)]), .coreInstance (.instantiate 2 [])] ++
  SimpleI.exportsDefsAt [("get", getFt)] 3 1 0 [getSX] (SimpleI.importsDefs hostI 0).2

/-- **`trap.wat` in the reference machine's syntax.** -/
def trapRef : Core3Component :=
  (SimpleI.importsDefs hostI 0).1 ++
  [.coreModule (Binary.coreModule trapCM), .coreModule (Binary.coreModule call2CM),
   .canon (.lower 0 []), .coreInstance (.exports [("f", ⟨.func, 0⟩)]),
   .coreInstance (.instantiate 0 []), .coreInstance (.instantiate 1 [("env", 0)])] ++
  SimpleI.exportsDefsAt [("get", getFt)] 1 1 0 [getSX] (SimpleI.importsDefs hostI 0).2

end Silmaril.Wasm.Component.InstTestsRef
