# Optimization and stripping variants

These are real ELF bytes in ordinary Git, built by
[`scripts/corpus/variants.py`](../../scripts/corpus/variants.py) from the canonical
packages' pinned archives. The original `corpus/elf` objects remain intact.
[`corpus/matrix.json`](../matrix.json) indexes only completed, hash-checked outputs.
It separates source/build identity from content hashes, and records the hierarchy
project → version components → source identity → configuration → target → compiler
and flags → stripping/artifact. Version components retain upstream's spelling;
date/commit versions are not asserted to be semantic versions.

Each profile directory has:

- `build.json`: archive identities, exact image/recipe hashes, source-input paths and
  hashes, generated inputs, environment, licence, run ID and precise proof status;
- `unstripped/` and `stripped/`: ELF outputs, SHA256SUMS and measured receipts;
- `<object>.pair.json`: all executable sections' byte hashes, addresses and sizes
  compared across this exact stripping pair; original nonzero function symbols;
- `runs/`: measured stages, including two clean builds, stripping, pair checks,
  runtime tests and receipt extraction;
- `logs/`: complete command logs compressed with deterministic gzip headers;
- optional `upstream/` and `generated/`: additional exact upstream inputs and
  configuration-generated inputs. Unchanged upstream files reference the existing
  canonical source paths rather than duplicating them.

The runner uses an exact image ID, two genuinely fresh build containers and an
8 CPU / 32 GiB cap. Each pair of build outputs must match byte-for-byte. Both are
independently stripped and compared again. A separate reusable post-processing
container limits container churn; it does not replace either clean build.
The earliest receipts used fresh containers for every post-processing operation;
their commands and measurements record that distinction. Both stripping variants
must pass the existing package tests before a profile is published.

```sh
corpus/toolchain/image.sh
python3 scripts/corpus/variants.py --work /work/out/variant-builds
# Or a selected tranche:
python3 scripts/corpus/variants.py --package cjson --arch aarch64 --level O1 \
  --work /work/out/variant-builds --resume
python3 scripts/corpus/matrix.py --output corpus/matrix.json
```

Defaults cover all ten packages, both architectures, and O0/Og/O1/O3. Existing
completed profiles are never overwritten: `--resume` verifies output and included
source hashes and retains their original receipts without claiming new runs.
Builds not yet completed are absent from the matrix. The existing canonical O2
unstripped artifacts are indexed too; O2 stripped artifacts are not yet delivered.

The paired executable-byte check supplies tool-derived stripped address mappings,
not functional equivalence, source-semantic binding or a Lean proof. The new
variants have **no generated/checked Lean parsing or structural decompositions**
and **zero contextual C-to-ELF or binary-equivalence statements**. Source mappings
and those formal stages must be added separately. This tranche adds optimization
and stripping variants of existing releases; it does not provide the requested
rich multi-version/configuration matrix or assembly-enabled OpenSSL/BoringSSL.

These inputs and outputs are [software under test](../UNDER-TEST.md). Owned build
scripts and local helpers retain normal code scanning; no findings are dismissed
or scans disabled by this representation.
