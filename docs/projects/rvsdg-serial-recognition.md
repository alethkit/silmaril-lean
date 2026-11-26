# Recognizing numbered serial RVSDG graphs

`Serial.Recognize.recognize` takes the actual numbered graph at the typed
entry and exit interface of the [serial bridge](rvsdg-serial-cuts.md).
There is no source CFG, spine, or cut certificate argument. The scanner
reads the outer table as alternating θ regions and typed connectors,
beginning and ending with θ. Each connector's opcode supplies the two
stage carriers and the common payload type. The child of each θ supplies
its actual local label tree and the recursion bound for the shared loop
parser. The parser checks header, join, and entry types and interprets
sequences and choices using the same local grammar as the numbered cut
recognizer.

The scan and parse propose a left fold of the observed leaves. Exact
certification compares the resulting graph with the input table. On
a composite it uses `Serial.certifyCut` at the last cut, which checks the
whole reconstructed table and therefore every earlier cut, every local
child, and all data and token origins. A singleton uses the same graph
equality checker. This comparison is what rejects stale wires even when
the typed labels and carrier kinds would otherwise parse.

A successful match contains a `Serial.Decomposition` indexed by the
actual input graph. Its `recover` constructs a typed flat LambdaSSA CFG
using the existing linker. `sound` gives the agreement with actual
`Region.denote` in coherent `StateT σ Part` models. The decomposition
retains the checked token witness and the equivalences for finite typed
exit, payload and exact final token, and for absence of finite return.
The SSA observation groups blocking and divergence under absence of
finite return.

`complete` covers any nonempty left-associated serial compiler spine
whose leaves have right-associated sequences of typed instructions and
binary γ. Each γ arm can itself contain sequences and choices. The proof
shows that checked relocation preserves the read marks and that appending
concatenates them. Each emitted θ supplies sufficient fuel for the local
parser, and the scan exactly recovers the original spine on this class.
The executable parser chooses one grouping. The completeness theorem is
for that grouping and the literal emitted layout. Arbitrary renumbering,
all associations of outer splices, nested θ in a leaf, and general CFG
structuring are separate.

The fixture runs recognition directly on the three-loop numbered graph.
The certified recovered region retains the observed intermediate tokens
6 and 9 and returns payload 23 with token 12. The stale second-cut graph
still yields a label candidate, then fails the exact check. A separate
executable fixture exercises an asymmetric binary choice and a multi-call
arm.

[API](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Serial/Recognize/Thms.lean) ·
[Fixture](../../tests/ssa/RVSDGLambdaSSASerialCuts.lean)

## Reproduce

```sh
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §§4.1.2–4.1.3 and 6.1. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
- Jad Ghalayini and Neel Krishnaswami, *The Denotational Semantics of SSA*
  (2024), arXiv:2411.09347v1, §§3, 5.1 and 5.3. PDF SHA-256
  `5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
  [Versioned PDF](https://arxiv.org/pdf/2411.09347v1)
