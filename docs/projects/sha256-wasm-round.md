# SHA-256 round word compiled to WebAssembly

`Silmaril.Wasm.Examples.Sha256Round.Thms` checks a second compiler target for
one expression in SHA-256. The fixture computes the updated working word
`a = T1 + T2` of FIPS 180-4 §6.2.2 from nine unsigned 32-bit operands.
`b` through `h` after the round, block parsing, the schedule and padding are
outside this comparison. [FIPS PUB 180-4](https://doi.org/10.6028/NIST.FIPS.180-4)

The reference is the first projection of the existing
`Silmaril.Crypto.SHA256.Kernel.round`. `Silmaril.Crypto.SHA256.compressRound_toBitVec`
relates the list specification's UInt32 round to that kernel for all inputs.
These are the existing Moria-derived developments introduced by the public
process promotion. [Public introduction](https://github.com/hiloopai/silmaril-lean/commit/a6c827c0171acf1c284e604870933501079bcdd2)

## Proved connection

- `decode_fixture` selects the named export from the exact bytes with the
  existing Core decoder. It checks the import-free function index, signature
  `(i32 × 9) → i32`, zero additional locals, and the 47 instructions.
- `run_fixture` proves that the existing Core interpreter stops after
  at most 48 driver iterations with the new `a` as its only stack value.
  It quantifies over all nine input words and every `d`, and preserves
  the frame and store. The proof checks the emitted left rotations against
  the specified right rotations, the two Boolean rewrites against `Ch` and
  `Maj`, and the changed order of modular additions.
- `steps_fixture` uses interpreter soundness to yield the corresponding
  host-free Core `Steps` derivation from a well-typed entry configuration.

The execution boundary is the function body with its parameters already
initialized in the frame. Module instantiation, the external call ABI and
compiler correctness are outside the theorem. The finite native test invokes
the export through Node's WebAssembly engine. Security and certification
claims are outside the comparison.

## Reproduce

```sh
tests/crypto/sha256-wasm/check.sh --lean-only
tests/crypto/sha256-wasm/check.sh
```

The Lean check builds with warnings as errors, checks a published intermediate
value in the kernel and audits the three public theorems transitively. The
full command also rebuilds the freestanding [C source](../../tests/crypto/sha256-wasm/round.c)
with Debian trixie amd64 Clang/LLD 19.1.7, package version `1:19.1.7-3+b1`.
It checks the resulting 149 octets against both the SHA-256 below and the
Lean literal, then runs the first two published `abc` round values under
Node's WebAssembly engine. [NIST SHA-256 intermediate values, pp. 1–2](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA256.pdf)

| Artifact | SHA-256 |
| --- | --- |
| C source | `b9c9c72d2ae9f5e6d121d5434a93a251a87eab44e1c075130ce1c3f2f76e970a` |
| Linked Wasm module | `4d31b21692befdabad18e921322665a49b056a83e96f18610556c9147225ff87` |
| Debian `clang-19` package | `bbb74458d782b7792b61b0eed92746df5e6d033778c045cf8c2b3835b7c4efc4` |
| Debian `lld-19` package | `756a805e8811d527dd2b5417f016c9342b8631fa9c1ddcd56265c13ae33bf3a4` |
