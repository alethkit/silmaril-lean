# Official SQLite 3.54.1 web release in Lean

This fixture consumes `jswasm/sqlite3.wasm` from SQLite's published
WebAssembly and JavaScript ZIP. The shipped `sqlite3.mjs` identifies SQLite
3.54.1, version number 3054001, and Emscripten SDK 5.0.1. Its source ID
contains Fossil check-in
`555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76` dated
2026-10-16 14:45:20. The released source archive's `manifest.uuid` and
`VERSION` match.
[Official download catalogue](https://sqlite.org/download.html) ·
[Source check-in](https://sqlite.org/src/info/555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76)

| File | SHA-256 |
| --- | --- |
| [Release ZIP](https://sqlite.org/2026/sqlite-wasm-3540100.zip) | `85ebce90b6d189442b29e11d193337b5e63203aae9b6590dbe89a601b9891da2` |
| [Source ZIP](https://sqlite.org/2026/sqlite-src-3540100.zip) | `387e7f6cad4797b17848c07d453dc6606917bb356a6cfe5a3abafd38c240c71b` |
| `jswasm/sqlite3.wasm` | `10fd727b37924755edc12c2f3ead0d54155d8f2d9f2abf6a1ef9b2b2597e0a51` |
| `jswasm/sqlite3.mjs` | `7f66120f5bb79d0646af88f5c27510ed26d731e801d96e4024d24878dec5a86a` |

The published ZIP SHA3-256 is
`87e24f6a4588692310b7942dc2fa7c7275bb9ba2e01d553e4115aa4a904a0050`.
The shipped JavaScript retains its SQLite public-domain dedication and
Emscripten license notices. The recipe extracts the published bytes.
[SQLite dedication](https://sqlite.org/copyright.html) ·
[Emscripten license](https://emscripten.org/docs/introducing_emscripten/emscripten_license.html)

## Reproduce

From the repository root, using its pinned Lean and Lake and a prepared
Lake dependency cache:

```sh
work=.lake/sqlite-web
mkdir -p "$work"
curl -fL https://sqlite.org/2026/sqlite-wasm-3540100.zip \
  -o "$work/sqlite-wasm-3540100.zip"
tools/sqlite-web-wasm/check.sh "$work/sqlite-wasm-3540100.zip" "$work"
```

The check is offline after the download and dependency preparation. It uses
the shared generator with the `sqlite-web` manifest to produce
`SqliteWebWasm.sqlite : Silmaril.Wasm.Module` and writes the canonical
replay to `$work/canonical.wasm`. All generated source, quotation inputs
and compiler outputs stay in the work directory.
[Release manifest](release.json) · [Generator entry point](../sqlite-wasm/quote.sh)

The binary imports 26 functions and one memory from `env` and nine functions
from `wasi_snapshot_preview1`. It declares 2,706 functions and exports
266 functions and the table `__indirect_function_table`. The start section
names function 36. The exports `__wasm_call_ctors`,
`sqlite3_libversion_number` and `sqlite3_open_v2` name functions 35, 483 and
550, respectively. The DataCount section declares 428 segments. The code contains zero data-index
operands, so the existing code-group decoder handles the fragments. The
generator preserves DataCount and the original data in the metadata
fragment. The re-encoder follows the original DataCount section policy.
The assembled object and the fresh original decode re-encode to the
same 879,430 bytes as the release binary in this executed check.

## Browser check

The shipped JavaScript wrapper supplies the browser host. The smoke check
loads that exact wrapper over loopback HTTP and executes in-memory SQL.
It accepts a Chromium executable and a Node module path containing
Playwright. The measured environment used Playwright 1.64.1 and Chromium
156.0.8078.4.

```sh
NODE_PATH=/path/to/node_modules node tools/sqlite-web-wasm/browser.mjs \
  "$work/release" "$work/release/jswasm/sqlite3.wasm" /path/to/chromium
NODE_PATH=/path/to/node_modules node tools/sqlite-web-wasm/browser.mjs \
  "$work/release" "$work/canonical.wasm" /path/to/chromium
```

The browser check reports the raw import and export inventory and checks
the SQLite source ID, version number and SQL result. The original and
replayed bytes both reported SQLite 3.54.1 and returned 42. The Lean
observations cover Core decoding and canonical replay.
