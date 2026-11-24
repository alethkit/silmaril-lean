# Named logic interpretation manifests

A syntax CID addresses an encoding of a syntax object. An interpretation gives
that syntax a judgment in a particular logic. Lean evidence establishes a
particular judgment. Each of those can change independently. For example, the
same HOL Light proposition `truth ⇒ truth` appears both as a closed kernel theorem
and as valid in a particular model. The two claims share the same syntax address
in each profile.

## Versioned records and identity

The optional `silmaril.named-logic.v2` sidecar adds a `claimIndex`. Its records
are the following.

| Record | Meaning |
| --- | --- |
| `syntax` | A stable syntax key resolves to a primary `{profile, cid}` and explicitly listed alternate profile addresses. The existing `profiles` and `blocks` own the profile metadata and original wire. |
| `logics` | A versioned logic ID fixes the logic family, exact signature and object theory. The pilot uses `HOLLight.initialSignature` and an explicit empty list of added axioms. |
| `interpretations` | A versioned interpretation ID and its logic. The kernel interpretation fixes the calculus and its checked judgment predicate. A model interpretation fixes the construction, parameter instantiations (universe in this case), predicate, pinned definition, Lean version and imports. A future model-family interpretation must declare its domain and model quantifier. |
| `claims` | A versioned claim ID links logic, interpretation, mode, an ordered sequence of `{role, syntax}` roots, context, assumptions and valuation scope. |
| `tables` | Stable table slugs scoped to a logic family, with presentation titles and ordered rows. Row IDs address navigation entries; each entry links a claim ID and can give it a display label. |
| `evidence` | A list per claim ID. Entries identify the evidence kind, source repository and full Git revision, Lean declaration and source path. The claim ID can have multiple independently pinned proofs. |

For the pilot, IDs are names assigned by the fixture author and versioned when
their meaning changes. A row slug and display label are navigation metadata.
A change to a signature, object axioms, calculus, model meaning, claim mode,
semantic coordinates, or scope requires a new versioned ID at the affected
level. Adding proof evidence, reordering table entries, or adding a validated
alternate address leaves the claim ID intact. Keep an existing table or row slug
stable for the same meaning. If a route must move, preserve an alias.

For comparison or a future canonical claim ID, resolve the logic and
interpretation to their versioned identities. Compare canonical syntax
coordinates in role order, the context, assumptions, and scope. Preserve order
for binders, typing contexts, and roles where order is meaningful. Normalize a
set of hypotheses only when the logic specifies set semantics and the
normalization is validated. An empty context or axiom list is explicit.
Distinguish a supplied valuation, a quantified valuation and a closed term,
including the treatment of type variables. Model truth under an assignment,
validity in one model, entailment from hypotheses and validity across a
quantified family are distinct modes or scopes. Evidence metadata and table
placement stay outside claim normalization. A content-derived claim ID would
require a separately specified canonical binary serialization.

Compare profile addresses as pairs. Cross-profile equivalence requires a
validated correspondence to the same canonical syntax. Here the external
verifier independently decodes each profile's bytes, computes the two digests,
and checks both references against the Lean encoder output. A successful
lookup or digest by itself gives no syntactic equivalence across profiles and
no judgment. Missing data is an availability condition. A refutation would
require evidence for a negative judgment with its own exact interpretation
and scope.

## The checked HOL pair

`HOLLight.Model.standard.{0}` is a concrete full set-theoretic model of the
initial signature, constructed in
[Consistency.lean](../../Silmaril/Logic/HOLLight/Consistency.lean). The
[carriers](../../Silmaril/Logic/HOLLight/Semantics/Type.lean) use lifted
two-valued Booleans, lifted naturals for individuals, and full function spaces.
There are no added constant interpretations in the initial signature.

The original kernel fixture has
`Examples.HOL.closedProof : Database.HOL.ClosedProof initialSignature [] closed`.
The [new fixture theorem](../../Silmaril/ProofFormats/DaslSyntax/Database/Examples/Model/Thms.lean)
is `Examples.HOL.standardValidity : HOLLight.Valid Model.standard.{0} closed`.
It applies `HOLLight.Derives.sound` to the derivation inside `closedProof`,
instantiates the standard model, and discharges satisfaction of the empty added
theory and truth of the empty hypotheses. `Valid` quantifies over type and free
term valuations in that one model. The related `standardValidityRow` uses the
existing abstract name and `Database.HOL.validIn`. Both results use the empty
added theory. The validity evidence is scoped to the specified model, with
separate evidence for kernel derivability.

The Lean exporter takes a term and proofs of both propositions indexed by that
term, then calls the HOL grammar on the same term. The external verifier checks
the rendered syntax, both profile CIDs and all claim, interpretation, table and
evidence fields against that export plan. Its input of trust is the plan
generated by the checked exporter. Authenticating a checkout and replaying Lean
are separate from external rehashing. The Explorer displays the pinned evidence
references, parses the selected wire locally, and rehashes SHA-256 where Web
Crypto is available. Read external verification in the verifier output and
proof checks in the Lean build or replay output.

## Version support

Use exact format tags to negotiate, with the plan and sidecar versions matched.
`check.sh` emits v1 by default; consumers restricted to v1 can keep that input.
The updated Explorer accepts v1 and v2, including existing row and profile URLs.
The v2 pilot carries the original v1 rows so the other HOL and MLTT judgments can
continue to browse without inferred semantic metadata. Only the closed HOL pair
has full v2 claims. The v2 fixture reader handles closed derivability and
single-model validity. Support for other modes and contexts requires a defined
encoding and a reader that understands it. Readers report an error for
unsupported versions.

See the [local commands](../../tools/verification-projects/named-logic/README.md#browse-the-standard-model-fixture).
