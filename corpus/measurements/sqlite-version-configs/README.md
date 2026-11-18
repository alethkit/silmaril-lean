# Delivered SQLite versions and configurations

These are actual public upstream release inputs and built ELF bytes, not version labels over one source tree. [artifacts.csv](artifacts.csv) maps every counted row through version → upstream Fossil source ID/archive SHA256 → configuration → target triple → compiler/flags → optimization → stripping → artifact/receipt/census/strip pair. [summary.json](summary.json) counts exact content hashes independently from rows.

| Upstream release | Delivered targets | Configurations | Levels | New ELF rows | Unique ELF hashes |
| --- | --- | --- | --- | ---: | ---: |
| [3.46.1](3.46.1/summary.json) | x86_64, AArch64 | default, FTS5+RTree, small | O0, O2 |48|40|
| [3.50.4](3.50.4/summary.json) | x86_64, AArch64 | default, FTS5+RTree, small | O0, O2 |48|40|

| [3.54.1](3.54.1/summary.json) | x86_64 | default O2, FTS5+RTree, small | O0, O2 |20|18|

All116 new rows/98 unique hashes/58 stripping pairs have actual bytes and source/recipe/tool/command/runtime/census receipts. All435 measured commands exited successfully. Version, archive, C source and Fossil source IDs differ genuinely. Some shell outputs are identical across configurations; row count does not count them as unique bytes. Source IDs are read from upstream C; exact runtime version observations are separate.

The default configuration enables threading. FTS5+RTree enables both extensions and actually exercises insert/search/range queries. Small disables threading, extension loading and default memory-status tracking, with recorded compile options. Both clean repeats and stripping forms pass the package smoke tests. Each repeated build uses its own initialized container and clean private workspace; those same two workers are reused across profiles. Full installed-package locks and immutable image IDs, sources, commands, flags, timings and decoder limitations remain in receipts.

This collecting draft continues with AArch64 3.54.1 profiles. Native default O0 is retained with its original receipt and no new execution claim. New sources were compared byte-for-byte against members of each exact hash-verified upstream ZIP. Those unfinished profiles are not counted above. No existing canonical/variant bytes are replaced. Public upstream source is under test; owned recipe/measurement code is separate. Public-domain dedications remain in included source headers. Census and runtime evidence establish no semantic equivalence, source binding, Lean proof or exhaustive testing. Full local make check was not run. Shared indexes/UI/DB/Lean remain owned by integration.
