# Actual corpus metadata database generation baseline

`database.py` generated the actual 106-artifact catalog, with 45,681 function
mapping rows and measured-stage receipts, in **1.165 s wall**, 0.950 s user CPU,
0.200 s system CPU, **72,580 KiB peak RSS**. Exit status 0; SQLite quick_check passed.
This is one sequential run with unspecified cache state, not a cold/warm comparison.

The [run receipt](runs/b2aa9a8a-36ad-4eba-8b7e-604844b8a9ce.json) records the actual
command, input/script hashes, repository state, pinned Lean version (not executed
by this stage), runner and measurements. The output is generated from completed
Git ELF artifacts and their receipts; it contains metadata, not ELF byte blobs.

This stage includes hashing/validating those ELF inputs, reading corpus metadata,
function mappings and stage receipts, and SQLite insertion. It excludes acquisition,
C compilation, Lean parsing/decomposition/kernel checks, canonical project export,
and semantic problem/proof generation. It is not an end-to-end pipeline timing.

Reproduction and browser checks: [scripts/corpus/README.md](../../../scripts/corpus/README.md).
