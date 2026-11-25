# Typed block compression

`Silmaril.Crypto.BlockCompression.Thms` gives a compressor a chaining
state type and an exact octet block length. `chain_append` composes adjacent
block sequences, and `chain_commutes` lifts a one-block state translation
to any finite sequence. `HashFn.digestVector` gives an existing complete
hash output its declared length, with a theorem that reading it as a list
recovers the original digest.

The SHA-256 instance in `Silmaril.Crypto.BlockCompression.SHA256.Thms`
requires 64-octet blocks. It proves that parsing gives 16 big-endian words
and that the existing UInt32 and BitVec compressors agree, under the
existing state translation, on any sequence of such blocks and any initial
state. The one-block proof reuses `SHA256.processBlock_eq_compressBlock`.
[FIPS PUB 180-4](https://doi.org/10.6028/NIST.FIPS.180-4)

Padding and framing belong to callers of the block interface. Hash digest
length and block length carry no TLS or QUIC message, key usage, record, or
packet bounds. The interface asserts functional laws about chaining and
representation.

```sh
lake build --wfail +Silmaril.Crypto.BlockCompression.SHA256.Thms +Silmaril.Crypto.HashFns.Defs
lake env lean -DautoImplicit=false -DwarningAsError=true tests/crypto/block-compression/Check.lean
```
