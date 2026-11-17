# Canonical OpenSSL whole-file checks

The x86_64 and AArch64 `libssl.so.3` reader bodies are split into bounded chunks
and assembled into whole-file parse theorems. Both `Decomp` roots passed
`lake build --wfail` in run `1d4a29de-011e-49b5-8852-c720993a7962`:
620.983 seconds wall, 6,633,060 KiB maximum child RSS, two configured workers.
The receipt binds all generated Lean modules and both ELF inputs by SHA256.

Canonical coverage is 51/54 whole-file parses with structural decomposition.
The two libcrypto files and AArch64 openssl executable still have checked layout
and structural decomposition only. These checks establish no execution semantics,
instruction-decoding correctness, control-flow correctness or semantic proofs.
