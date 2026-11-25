# Adler-32 initialization through a Core instruction shape

`ZlibWasm.initialization` quantifies over an arbitrary store and 32-bit
seed. For a function with an `InitWitness`, `initResult s seed f` returns
the unchanged store and `adler32OfList []` at fuel 32. The call frame
supplies `(seed, 0, 0)` and the four local declarations identified by
the witness. The two skipped branch tails are arbitrary. The proof uses
reduction in the existing Binaryen fuel interpreter.
[Theorem and witness checker](InitCheck.lean) ·
[Adler-32 model](../../Silmaril/Formats/Compression/Checksum/Adler32.lean)

```sh
tools/zlib-wasm/check-init.sh
```

The command checks the pinned Wasm digest, parses the whole module with
the ordinary Core decoder and resolves `adler32_z` through its export.
The witness checker matches the visited instructions and constructs the
body and local-type equalities used by the theorem. That connection to the
pinned file is an executable check. Lean checks the conditional interpreter
theorem in the kernel, and the command prints its axiom dependencies.

The result covers initialization with a null buffer and length zero. It
leaves nonempty checksum updates, interpreter adequacy and a kernel theorem
relating the pinned bytes to the decoded body to separate work.
