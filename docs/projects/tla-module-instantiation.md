# First-order TLA+ module INSTANCE

Import `Silmaril.Logic.Temporal.TLA.Resolution.Instances.Defs` and call
`Instances.check registry root externalLevels`. Its result pairs the resolved
registry with the level certificate built from that graph. The checker uses
the caller's per-module registry map for both `EXTENDS` and `INSTANCE`. Each
edge resolves an identity and checks the declared module header. Cycles can
cross either kind of edge.

The existing core and level syntax profiles retain their scope. The instance
entry point selects `.instanceSyntax`, which adds module-level named and
anonymous INSTANCE, including LOCAL, and qualified references to their
exported operators. Nested instances through registry modules can be selected
with calls such as `I(a)!J(b)!Op(c)`. Arity is checked separately at each
segment. Each named INSTANCE reserves a bare namespace name. LOCAL members
are usable in their host module and excluded from its exports.

[Instance API](../../Silmaril/Logic/Temporal/TLA/Resolution/Instances/Defs.lean) ·
[Module resolution](tla-module-resolution.md) · [Expression levels](tla-expression-levels.md)

## Substitutions and level checks

- WITH targets are constants and variables from the instancee's declaration
  view, including declarations inherited by `EXTENDS`. Defining operators
  and local names are ineligible. Targets must be unique and every declaration
  needs a replacement, including unused declarations.
- Explicit RHS expressions are resolved in the host scope at the instance
  declaration, with any named instance formals. Each omitted target resolves
  by the same spelling in that host scope. A same-named nullary definition
  is a valid replacement. Other replacements must meet the expression arity.
  WITH entries take effect simultaneously. Every RHS reads its host context,
  including when both modules inherited the same declaration ID.
- For a nonconstant instancee, a declared constant's replacement must have
  constant level and a declared variable's replacement must be at most state.
  The checker classifies the instancee using its original checked declarations
  and definition levels. For a constant instancee it checks the substituted
  bodies against their operator and structural constraints. For example,
  `Out == C` may acquire action level through `C <- v'`. A set enumeration
  `Out == {C}` rejects a temporal replacement, even in a constant module.
- Level checking replays the instancee and its EXTENDS closure in a private
  operator table. It retains the specialized member summaries and restores
  the original table. A nested instance checks its RHSs in the current replay,
  then checks its own target with a fresh substitution environment. Ceilings
  on named instance formals become call requirements, even when the selected
  member ignores that replacement. Replay failures report the host instance
  site and the underlying home-site diagnostic.
- Repeated named instances have distinct IDs. An anonymous instance with
  no substitutions can reuse the original exported identity, including
  after an identical EXTENDS path. Other unqualified collisions are errors.
  The pinned SANY frontend can warn and keep the first binding when two
  parameterized anonymous instances export the same name. This profile
  also diagnoses collisions involving a nonempty environment and a shared
  parameter-free origin.

[Specifying Systems, §§4.2, 17.5.5 and 17.8](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=348) ·
[Pinned SANY WITH checking](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/semantic/Generator.java#L5247) ·
[Pinned SANY level checks](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/semantic/InstanceNode.java#L145)

## Evaluator handoff

`CheckedInstances.instanceAt site` retrieves the checked plan for a source
declaration. `CheckedInstances.memberAt bindingId` retrieves the plan and a
generated member's `home` binding ID. The home binding may itself be a
generated member. Resolve qualified calls with `qualifiedCall` and
`qualifiedArguments` when the evaluator needs their positional actuals.
A parameter-free anonymous reuse goes directly to its home identity.

Existing `BindingId` and Surface paths stay stable. A synthetic member appends
`.instanceMember i` to the instance site. Instance formals use
`.parameter i`. An explicit RHS and its resolved references start at
`.substitution i`. In a qualified application the reference is at the
whole call's site. Its head arguments use `.argument j`, and selector
arguments use `.selector i, .argument j`. Qualified names have a
`Name.qualified` key. Bare namespace bindings have kind `.instanceNamespace`
and are not called as operators.

To replay an accepted member, use the first arguments to bind the instance
formals and pass the remaining arguments to the home binding. Keep actuals
as expressions in their caller environments. Evaluate each replacement
expression using its stored host site, or use its captured implicit host ID.
Both are interpreted in the captured host frame with the named instance
formals. The current valuation is the one at the home use. Under prime that
is the target valuation. The same home binding and its LOCAL helpers may
be used by several instances, so key any evaluator memo by the environment as
well as the home identity. When a home binding is itself a member, replay
its plan in the enclosing instance environment.

The level certificate has a summary at each generated member ID.
`expressionAt` continues to describe original source sites in their own
module contexts. Specialized child annotations belong to the replay and
are not installed as global changes to those sites.

## Scope and checks

This increment rejects operator-valued targets and replacements, operator
formals of an instance namespace, LET instances, submodules, recursive
operators and cyclic module graphs. The instancee and its EXTENDS closure
require parsed source. A theorem or assumption in that closure is outside
the instance profile. ENABLED in replayed bodies is rejected because
§17.8 requires special treatment for its implicit bindings. The other
implicitly binding action or temporal forms remain deferred. The result
checks syntax and levels without defining values or discharging proofs.

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.Resolution.Examples \
  +Silmaril.Logic.Temporal.TLA.Resolution.Levels.Examples \
  +Silmaril.Logic.Temporal.TLA.Resolution.Instances.Examples
```

The parsed regressions check nested and repeated instances, lookup through
EXTENDS, private helpers, cross-module name capture, implicit and explicit
replacement identity, per-segment arity, direct and deferred ceilings, and
unchanged home summaries. The nested fixture was also accepted by the
pinned SANY frontend with matching levels for its three selected definitions.

[Instance regressions](../../Silmaril/Logic/Temporal/TLA/Resolution/Instances/Examples.lean)
