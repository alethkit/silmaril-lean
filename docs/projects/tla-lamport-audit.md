# Standalone TLA audit against Lamport

This audit covers the typed Simple TLA and scoped General TLA described in the
[project guide](tla.md). Its reference is Leslie Lamport, *The Temporal Logic of
Actions*, ACM TOPLAS 16(3), May 1994, pp. 872–923, DOI
`10.1145/177492.177726`. The section and figure numbers below refer to the
author-hosted November 1993 camera-ready PDF, SHA-256
`47b8e7844b0ca7a7ce4cf31bad2df887307e796450f36520bbdc078516b8278e`.
[Author-hosted PDF](https://lamport.azurewebsites.net/pubs/lamport-actions.pdf)
· [Published article](https://doi.org/10.1145/177492.177726)

## Simple TLA

| Paper | Lean definition or theorem | Coverage |
| --- | --- | --- |
| §§2.1–2.6 and Fig. 4, states, state functions, actions, priming and validity | `Behavior`, `StateExpr`, `StatePred`, `Action`, `Action.current`, `Action.prime`, `Formula.Sat`, `Formula.Entails` | Direct denotations over a chosen Lean state type. Priming reads the target state. Action validity is a Lean premise quantified over pairs of states. The paper interprets first-order expression syntax by simultaneous substitution in a universe of variable assignments. The standalone leaves are functions and relations, with no expression grammar, occurrence analysis or syntactic action validity judgment. |
| §2.7, equation (5), enabledness | `Action.enabled`, `General.StatePred.enabled` and `eval` | Direct existential over target states. The General state predicate exposes enabledness as a constructor whose action is still a denotation. The paper's syntactic expansion into fresh rigid quantifiers over the primed occurrences would require expression syntax and substitution. |
| §5.6, Fig. 4, temporal grammar and evaluation | `Formula`, `Formula.Holds`, `Formula.Sat`, `Formula.holds_suffix` | The five temporal constructors match the Simple fragment. Indexed box evaluation is proved equivalent to explicit suffix evaluation. The first two states supply action denotations inside steps. Bare actions and the unrestricted action box belong to the paper's RTLA discussion in §4. |
| §§5.1–5.3 and Fig. 4, unchanged, bracket, angle, eventually and leads-to | `Action.unchanged`, `bracket`, `angle` and `Formula.eventually`, `eventuallyAngle`, `leadsTo`; `Formula.holds_eventually`, `holds_eventuallyAngle`, `holds_leadsTo` | Defined from the primitive connectives and action semantics. The characterization lemmas derive their indexed witness laws. A bracket can permit changes to components outside its observation. |
| §§5.3–5.5, equations (17)–(18), fairness and program shape | `Formula.weakFair`, `strongFair`, `spec`; `holds_weakFair`, `holds_strongFair`, `strongFair_implies_weakFair` | The fairness definitions directly encode recurrence of changing steps or the respective disabledness clauses. Continuous-enablement and recurrent-enablement forms are derived. `spec` assembles the standard three conjuncts with arbitrary `Live`. A machine-closure criterion saying when fairness adds no safety constraints remains open here. |

[Simple definitions](../../Silmaril/Logic/Temporal/TLA/Defs.lean)
· [Simple theorems](../../Silmaril/Logic/Temporal/TLA/Thms.lean)

### Figure 5 rules

| Paper rules | Checked interface and gap |
| --- | --- |
| STL1–STL6 | Lean's propositional logic and the suffix semantics can discharge individual instances. There is no standalone derivation system or named suite for these rules, including STL1's criterion for propositional provability. |
| Lattice | No rule deriving progress from a well-founded ranking over a family of temporal formulas. |
| TLA1, TLA2 | The structural induction in `Formula.spec_invariant` gives invariant preservation under bracket steps. The TLA1 equivalence with the unchanged-observation premise and the TLA2 step-simulation rule have no standalone statement. |
| INV1, INV2 | `Formula.spec_invariant` gives INV1 with a separate initial condition and an arbitrary extra liveness conjunct. INV2's equivalence after strengthening the next-state relation with the invariant at both ends remains to be stated and proved. |
| WF1, SF1 | `Formula.weakFair_progress` gives a semantic WF1 variant. It assumes progress from any step of the fair angle action while waiting, so it can use an independent observation for that action. Fig. 5 uses the common observation and only needs progress on the intersection with the next-state relation. The exact WF1 premise and SF1's recurrent enabling argument under an additional always-assumption are absent. |
| WF2, SF2 | No fairness transfer rule with a separately evaluated target enabledness premise, as required for §8.3.3. `strongFair_implies_weakFair` compares fairness of the same action and observation. |

## General TLA and Figure 9

| Paper | Lean definition or theorem | Coverage |
| --- | --- | --- |
| §2.6 and Fig. 9, rigid variables and quantification | `General.Scope`, `Model`, `Expr.rigid`, `Expr.flex`, `Action.existsRigid`, `StatePred.existsRigid`, `Formula.existsRigid` and their evaluation clauses | Direct typed semantics. One rigid valuation is used throughout a behavior and at both ends of an action. A rigid binder extends that valuation once, choosing from one sort's carrier. The paper uses a common value domain. |
| §8.2 and Fig. 9, general formula grammar | `General.Formula`, `Formula.Sat`, `Formula.Holds`, `Formula.rename`; `Context.old`, `Context.fresh`, `Scope.Rename.underFlex`, `underRigid` | Scoped temporal syntax with denotational leaves and binders that add a fresh name of a selected sort. The Lean grammar also allows box directly over a quantified formula. Fig. 9's displayed General production only inherits box through its Simple-formula alternative. Renaming preserves the fresh name under binders. |
| §8.2, equations (48)–(49), and Fig. 9, stuttering and agreement away from the hidden name | `Retiming`, `StutterEquiv`, `StutterEquiv.retime`, `trans`, `map`, `hide_iff_lamport` | The code uses common expansions in place of the paper's canonical reduction `#`, and equality after projection in place of `=_x`. It proves equivalence-relation laws and the product-state form of (49) for stutter-invariant operands, phrased with `StutterEquiv`. A Lean definition of (48) and a theorem identifying equality of its reductions with `StutterEquiv` are absent. |
| Equation (49), flexible witnesses; §8.2, invariance | `hide`, `General.Formula.existsFlex`, `Formula.sat_existsFlex`, `Formula.sat_stutterInvariant`, `Formula.holds_retime` | The core projects a full witness and compares its visible run up to stuttering. `sat_existsFlex` derives the clause in extended valuation coordinates. Whole-state stuttering invariance holds for every scoped formula, including nested binders. `forallFlex` and `forallRigid` and their satisfaction characterizations are derived by duality. |
| E1, introduction with a state function | `General.Formula.existsFlex_intro` | The premise evaluates the body after extending the valuation at each instant with `f ρ s`. The term can depend on the outer rigid environment and visible state. That extension witnesses the quantifier without a change of clock. The unresolved syntactic result is a capture-avoiding operation `F(f/x)` on a chosen expression grammar and a theorem equating its satisfaction with this evaluation premise, including for nested binders and `ENABLED`. |
| E2, elimination with a fresh conclusion | `General.Formula.existsFlex_elim`, `Scope.Rename.weakenFlex`, using `Formula.sat_rename` and `sat_stutterInvariant` | The conclusion is typed in the outer scope. Its weakening forces independence from the fresh name. The proof transfers the weakened consequence along the witness's projected stuttering equivalence. A formulation for named syntax would need free-name analysis and a theorem that any syntactically fresh conclusion factors through weakening. |
| F1, introduction with a constant expression | `General.Formula.existsRigid_intro` | The premise uses `e ρ` as a single value for the whole run. The type of `e` permits outer rigid variables and excludes flexible-state inputs. The unresolved syntactic result is satisfaction of capture-avoiding `F(e/c)`, including rigid binders inside actions and predicates. |
| F2, elimination with a fresh conclusion | `General.Formula.existsRigid_elim`, `Scope.Rename.weakenRigid`, using `Formula.sat_rename` | The conclusion again lives in the outer scope and reaches the extended premise by weakening. A named syntax would need the rigid free-name and weakening factorization theorem. |

[General definitions](../../Silmaril/Logic/Temporal/TLA/General/Defs.lean)
· [General theorems](../../Silmaril/Logic/Temporal/TLA/General/Thms.lean)
· [Semantic rule statements](../../Silmaril/Logic/Temporal/TLA/Rules/Thms.lean)

## Auxiliary variables and refinement

- In §8.3.2, an auxiliary variable is justified by recovering the original
  specification after hiding. `hide_extension_iff` gives a sufficient criterion.
  Projection must satisfy the visible specification, which must be stutter-invariant,
  and every satisfying visible behavior must admit an extension with exactly
  that projection. Taking the same clock is a sufficient witness condition.
  The examples apply this to a history bit recording whether a visible bit
  has ever been high. The paper's general existence result for suitable
  auxiliary variables, including prophecy, remains outside this development.
- For equation (51), `hide_refines` transports a full-state simulation through
  the existential hiding on each side. Its state map computes the target hidden
  component from the full source state and computes the target visible component
  from the visible source state alone. Iterated binders and substitution of
  refinement expressions into named formulas are separate obligations. The
  existing `General.Refines.comp` composes maps and `hide_map_iff` is a
  visible-state pullback law for stutter-invariant operands.
- For §8.3.3, evaluate target enabledness in the target state space before
  pulling the resulting predicate back. `Action.enabled_pullback_iff` gives a
  sufficient condition for evaluating enabledness after action pullback instead.
  Every target successor allowed by the action from the mapped source must
  lift to an implementation state. For fairness the action in this hypothesis
  is the angle action. The checked diagonal example reproduces the distinction
  in §8.3.3 with Boolean values. A syntactic barring theorem must substitute only
  free occurrences, treating the successor variables in `ENABLED` as bound.

[Rule examples](../../Silmaril/Logic/Temporal/TLA/Rules/Examples.lean)

## Next PRs

1. Add a Simple TLA proof-rule module for TLA1, TLA2 and INV2, with a checked
   step-simulation example that uses an observation coarser than the whole state.
   Extend it with Fig. 5's exact WF1/SF1 and the WF2/SF2 rules with an explicit
   target enabledness predicate, preserving the distinction from §8.3.3.
2. Define the canonical stutter reduction from equation (48) and prove its
   equality criterion against common expansions, including behaviors with an
   infinite final block. Use it to state (49) with the paper's relation verbatim.
3. On a specified expression grammar, prove capture-avoiding substitution under
   priming, quantifiers and `ENABLED` and connect it to E1/F1 evaluation.
   Prove the free-name weakening criteria for E2/F2 in the same representation.

Figure 5 soundness beyond the listed theorems and the paper's relative
completeness result (§8.3.2 and Note 12) remain open. Build the standalone
rules and checked examples with
`lake build --wfail +Silmaril.Logic.Temporal.TLA.Rules.Examples`.
