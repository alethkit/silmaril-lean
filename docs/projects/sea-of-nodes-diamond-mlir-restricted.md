# Restricted scoped models for Sea of Nodes diamonds

Import `Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted.Thms`.
A `Presentation P` supplies an actual scoped MLIR model at the generated
signature, an equivalence from its predicate carrier to `ULift Bool`, and
an equivalence from each selector carrier to `ULift (Fin n)`. Data carriers
come directly from the scoped value sorts. The state alphabet is empty.
A `Restricted.Model P` adds two local operation laws after transporting
through those decodings.

- Dispatch uses the decoded Boolean to send true to selector 0 and false
  to selector 1. It forwards the two payload slots in their given order.
- γ calls the region chosen by the decoded selector, with the remaining
  operands as its parameters, and returns that region's yields.

The laws compare individual operation interpretations at their finite typed
profiles. Primitive symbols have zero regions and one result. `extract`
reads each primitive from that result slot after decoding and retains the
data carriers. The structural fields consist of scoped data, encodings, and
the two operation laws.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Diamond/MLIR/Institution/Restricted/Defs.lean)

## Change of signature and satisfaction

The scoped map fixes the sorts, dispatch, and γ. Consequently the same
decodings and laws apply after reducing a scoped model along that map.
`extract_reduct` proves that extraction commutes with this reduct.
`normalize_eq_induced` reconstructs the normalized model from extraction.
The proof checks the primitive case via the ordered tuple/assignment
round trip and uses the two local laws for dispatch and γ. Transport of
term denotation gives invariance under the encoding, including inside
isolated regions. This yields `satisfaction` on the original scoped model.

`Restricted.inst` uses scoped equations and discrete admitted models over
the diagram indexed by the generating diamond signatures.
`Restricted.comorphism` is a checked `Inst.CoHom` into that restricted
institution. Its signature functor is the identity on the indexing
category. It lowers sentences forwards and extracts models backwards.
The two naturality squares use the existing equation translation and the
extraction reduct law. The global scoped MLIR institution retains its model
category.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/MLIR/Institution/Restricted/Thms.lean) ·
[Signature translation](sea-of-nodes-diamond-mlir-naturality.md) ·
[Comorphism interface](../../Silmaril/Logic/Institution/Morphism.lean)

## Model boundary

The regression reverses the encoding of the finite selector. At raw
selector 1 it chooses arm 0 and yields false, while an induced model
chooses arm 1 and yields true. Decoding makes this model admissible, and
the checked observation separates it from the induced family.

The first-arm γ model from #3266 fails the γ law for any choice of
decodings. The singleton carrier from the other #3266 counterexample
admits no Boolean decoding.
[Boundary regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/MLIR/Institution/Restricted/Regression.lean) ·
[#3266](https://github.com/hiloopai/silmaril-lean/pull/3266)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```
