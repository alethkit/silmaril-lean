# Representative BoringSSL / BoringCrypto inputs under test

This is upstream BoringSSL at commit
[`ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6`](https://github.com/google/boringssl/tree/ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6).
BoringCrypto (BCM) is the cryptographic module in that same tree, not a separate
upstream project. These are non-FIPS research builds. They are not certified or
validated, do not define `BORINGSSL_FIPS`, and do not run integrity-hash injection.
Upstream FIPS_SHARED/FIPS_DELOCATE configurations are not built here.

The pinned corpus image is unchanged. The repository-authored `embed.py` consumes
upstream's committed `gen/sources.json`, as supported in upstream's
[Build support contract](https://github.com/google/boringssl/blob/ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6/INCORPORATING.md#build-support).
Its `bcm`, `crypto`, `ssl`, and `bssl` targets define the exact boundaries. The
BCM object-library branch in upstream `CMakeLists.txt` combines the BCM source and
assembly inputs; this recipe packages that same boundary with GNU `ld -r` before
linking it into libcrypto. The supplementary `boringcrypto-bcm.o` is ET_REL, not a
standalone executable or shared library. Its receipt includes relocation and
unresolved-symbol requirements. Both repeats must match. It is preserved
unstripped; no strip-all linkability or symmetric module stripping claim is made.
The linked libraries and bssl have independently compared stripping pairs.

Configuration `no-asm` omits the assembly source lists and defines
`OPENSSL_NO_ASM`. Configuration `asm` compiles the upstream assembly lists;
upstream preprocessor/platform guards select the actual architecture. The `.S`
files in `gen/` were generated upstream and are consumed verbatim as pinned source
inputs. No generator is invoked here; included `.pl` and pregeneration sources are
available provenance, not evidence of execution or the historical generator's
tool version. `embedding-plan.json` records planned commands; `embed-build.log`
records executed Make commands. Depfiles preserve actual compiler inputs and
headers; exact raw input/archive hashes remain with the completed profile.

Smoke tests use the actual shared libraries for SHA-256/AES known answers,
Ed25519 signature acceptance/rejection, certificate signatures and a TLS 1.3
handshake/application transfer over a BIO pair. The CLI runs its sha256sum and
cipher enumeration commands. AArch64 runs under the pinned QEMU. These are
specific observations, not exhaustive upstream tests, semantic proofs or FIPS
validation. The TLS test checks a certificate signature separately; it does not
exercise certificate-chain/path validation or network I/O.

```sh
corpus/toolchain/image.sh
python3 scripts/corpus/variants.py --package boringssl --configuration no-asm \
  --configuration asm --level O2 --work /work/out/boringssl-pool
```

Only completed variant receipts count as delivered artifacts. This recipe and
source selection alone do not assert that a profile has been built.
