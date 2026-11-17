# Measured variant Lean checks

Two real cJSON 1.7.19 x86_64 O0 libcjson_utils variants (stripped and unstripped) have whole-file ELF parse and structural decomposition checks. `checks.json` binds exact artifact and generated-module hashes to the successful run receipt. The matrix rejects stale module hashes.

The same run checked the canonical x86_64 OpenSSL CLI whole-file parse using bounded symbol and relocation table chunks. This brings canonical whole-file parses to 49 of 54; five large OpenSSL files still have only checked layouts/decompositions. Of 192 delivered variants, two are checked here and 190 remain unchecked.

Run 1448c969-1ac0-43ae-845a-b92fe332cda5: 210.215 s wall, 379.35 s user CPU, 46.31 s system CPU, 4,085,804 KiB maximum child RSS; two Lean workers. Includes dependency work and warm caches; not a clean isolated elaboration benchmark. The receipt records inputs, toolchain and command. An earlier monolithic attempt was stopped and is not a successful measurement.

These are structural proofs, not instruction semantics, translation validation, or functional equivalence. Both semantic statement counts remain zero. Stripped decompositions use retained symbols and gaps; external paired symbol maps do not become Lean-proved symbols.
