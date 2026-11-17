# Corpus evidence and measurements

`census.py` reads every canonical `corpus/elf/*/*/receipt.json`, verifies each ELF's
SHA-256, and writes one JSON report per artifact. Run it in the pinned corpus
toolchain image; it needs native and AArch64 GNU binutils. It does not execute the
artifacts. The reports contain receipt identities, `DT_NEEDED`, SONAME, interpreter,
version requirements, imports, relocation types, TLS/IFUNC indicators, exact import
matches for selected ABI features, executable-section mnemonic counts, bounded
exact-mnemonic extension evidence, and syscall instruction sites.

```sh
corpus/toolchain/image.sh
docker run --rm --network host --cpus 8 --memory 32g \
  -e CORPUS_ANALYSIS_IMAGE_ID="$(docker image inspect --format '{{.Id}}' silmaril-corpus-toolchain:trixie-20251103)" \
  -v "$PWD:/repo:ro" -v /work/out:/out -w /repo \
  silmaril-corpus-toolchain:trixie-20251103 \
  python3 -I scripts/corpus/census.py --output /out/census
python3 -B scripts/corpus/test_census.py
python3 -B scripts/corpus/test_measure.py
```

This is tool-derived evidence, separate from Lean parsing/decomposition proofs and
machine semantic support. Linear decoding may interpret data as instructions. All
executable sections are listed, including sections with no disassembly output.
Decoded, undecoded and unreported byte counts stay separate. The extension
classifier is intentionally incomplete and publishes its allowlist in each report.
An empty match is not evidence that an extension is absent. A syscall site is not
a runtime observation; syscall numbers are left unknown. Imports are potential
dependencies, not demonstrated runtime use. Static dependencies, indirect calls,
signals, futex behavior and vDSO use need further analysis or observation.

`measure.py` runs one explicit command and writes a fresh UUID-named JSON record.
It records repository/input/tool hashes, command, target, declared cache state and
concurrency, runner capabilities and cgroup limits, wall time, child CPU time,
Linux peak RSS and exit code. Run it **inside** the container to measure the actual
tools: wrapping `docker run` measures full wall time but only Docker-client CPU/RSS.
`--repository-receipt` accepts the host's Git revision/dirty/diff hash as JSON when
the pinned container has no Git. Keep independent runners' records and merge files;
there is no shared writable measurement database. Concurrency is recorded, not
enforced by this wrapper. Use the container limits and tool-specific job limits.

Measure acquisition, compilation, ELF parsing, function extraction, decomposition
generation, Lean elaboration/kernel checks, project dump/export, SQLite generation,
and semantic problem/proof stages separately when they run. Do not infer a stage's
cost from an aggregate command, or claim a run for a stage that was not executed.

`db_benchmark.py` exports an existing SQLite database as SQL (optional) and replays
the SQL into a **new** database, checking SQLite integrity and reporting table
counts, SQL hash and materialization wall time. It never replaces the input.

```sh
python3 scripts/corpus/measure.py --stage sqlite-export-and-materialization \
  --output /work/out/runs --target host-sqlite --input INPUT.sqlite -- \
  python3 -I scripts/corpus/db_benchmark.py --database INPUT.sqlite \
    --sql /work/out/input.sql --output /work/out/replay.sqlite
```

For repeats, omit `--database` and replay the saved `--sql` into a different new
output. SQL and output databases retain the input's disclosure restrictions. This
benchmark measures SQLite materialization, **not** Lean elaboration, project
validation, canonical project SQL generation, or end-to-end regeneration. No ELF
byte-storage representation is changed by these tools.
