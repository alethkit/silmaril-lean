# Free undefined behaviour in Isotope refinement

In the ordered institution, the inequation `a ⊑ b` is interpreted as
`⟦a⟧ ≤ ⟦b⟧`. In the observational institution it is inclusion of the
outcomes of `a` in those of `b`. UB, which permits every outcome, is on the
right of `t ⊑ ub`. A compiler contract can accordingly place the target on
the left and the source on the right. See [ordered satisfaction][ordered],
[observational satisfaction][obs], and [the compiler convention][compiler].

## Construction

The native term and region grammars have empty-type elimination. Literal UB
is introduced here through the extended presentation and the unit-fed
instruction spelling. [LetCase typing][case-typing] [LambdaSSA syntax][ssa-syntax]
[LambdaRTL syntax][rtl]

- `UB.dialectMonad e` acts on `InstrSig τ ε` for fixed types, effects, and UB
  effect `e`. A primitive has one typed input and one result. The new symbol
  at result type `A` has profile `unit → A` and effect `e`. A morphism
  extending a relabelling can choose any symbol with precisely that profile.
  The unbundled `SignatureMap` also changes types and effects. A corresponding
  lift needs to preserve unit and transport the chosen effect as well as the
  ordinary typing and effect premises. [Primitive extension][primitive]
  [Instruction morphisms][instr] [Varying signatures][sigmap]
- `UB.signatureMonad` acts on the contextual `PSig` used by the ordered
  institution. It adds a literal arity-zero operation per judgment sort.
  For LetCase and LetIter a sort includes a bound context and a result type,
  with the free-variable context fixed by the presentation. The independent
  explicit constructor `Expr.ub` has the unique fold into any algebra for
  the extended signature. [Explicit syntax][syntax] [Signature monad][signature]
- `UB.Specification.monad` acts on the institution's specifications. A map
  must send axioms to consequences. The extension transports the old axioms
  and adds `t ⊑ ub` for **every** term at its sort, including expressions
  under binders. `homEquiv` states the universal property for targets with
  designated nullaries above every denotable term. Restriction along the unit
  and extension using the designated symbols are inverse. In each monad the
  unit includes the old operations and multiplication identifies the inner
  and outer fresh symbols. In the ordered case the two symbols may still be
  distinguished before applying multiplication. [Specifications][spec]
  [Institutional consequence][institution]
- Monotone algebra operations place the inequalities under well-sorted
  constructors. The whole expression in any such context lies below UB at
  the result sort. An equation saying a context around UB evaluates to UB
  would need separate absorption laws. In arbitrary validating algebras the
  top rule bounds the image of the syntax fold. In the initial ordered
  quotient every element is represented by syntax, and `initial_le_ub`
  bounds the entire carrier at every sort. The ground inequations alone
  cannot constrain elements outside that image. `model_without_top` gives
  a two-point validating algebra whose carrier has no greatest element.
  [Ordered algebra and quotient][models]
  [Initial model][spec]

## Ordered LetCase bridge

`refinement_iff` preserves and reflects refinement between literal-unit
endpoints. `quotientIso` identifies the explicit quotient by mutual
refinement with the quotient of canonical native terms by the inherited
native order. The native presentation uses the full well-typed extended
dialect as syntax. Its generators are the relabelled original sentences and
`t ⊑ op (ub A) unit` for every native `t : A`. The proof uses monotone
constructor operations, retains the chosen primitive effect, and imposes no
purity requirement on it. Canonical elaboration always supplies literal unit,
so it never erases an effectful operand. Readback on arbitrary operands is
used internally to compare these generated axioms. [Bridge][case-refinement]

With the original sentences taken from `caseTheory`, `preserves_native`
also gives a derivation in LetCase's full native refinement calculus with
the transported primitive rules and the top rule. Reflection into the
original free extension fails for that stronger target. Native case beta
drops an unselected branch containing UB, even with effectful UB and
canonical endpoints. The Boolean occurrence model validates the interpreted
axioms and distinguishes the two terms. Its `true` is greatest and
`encode_eval` gives agreement with the induced explicit interpretation.
The flag includes both branches and describes UB occurrence in syntax.
[Model][case-model] [Checked counterexample][case-regression]

## Coverage and gaps

| Language | Refinement and institutions in the repository | UB construction and remaining hypotheses |
|---|---|---|
| LetCase | The exact typed preorder gives `caseTheory` and ordered algebra models. The separate operational institution observes results, faults and divergence. | Instantiate the ordered monad with `casePSig` or the specification of `caseTheory`. `typedEquiv` proves both typed round trips between explicit UB and native terms generated with `op (ub A) unit`, including under binders. The interpreted order preserves and reflects on these endpoints. Arbitrary unit-typed operands can have effects, and an operational equivalence needs to preserve their evaluation and justify the sequencing and UB laws in the chosen observation model. [Ordered theory][let-theory] [Typed round trip][case] [Ordered bridge][case-refinement] [Observations][obs] |
| LetIter | `iterTheory` gives ordered refinement models. The separate quantitative `Refinement.Thms` also has categorical initiality and singleton-input completeness. Operational stuckness yields an undefined outcome, while the observational institution tracks returns, faults and divergence. | The ordered monad applies to `iterPSig`. A native spelling round trip would extend the LetCase constructor proof with the iteration binder. For the quantitative calculus the unit operand requires `Γ.Discardable`; a literal UB at a linear context needs a new typing rule or a resource-consuming encoding and a proof of the directed effect and iteration laws. [Ordered theory][let-theory] [Quantitative typing][quant-typing] [Categorical initiality][quant] [Undefined outcome][iter-beh] |
| LambdaSSA | Typed terms use unary instructions and regions have separate value and label contexts. The typed CFG quotient uses `RewriteEquiv`. The observational institution has inclusion of outcomes, with an observational isomorphism to LetIter for single-exit regions. | The primitive monad supplies a unit-taking expression instruction. A top **region** needs a constructor or a terminating encoding at every label context, including an empty one, plus a typed ordered presentation and compatible label substitution and feedback. The observational isomorphism does not give these typing or top laws. [Typing][ssa-typing] [Rewrite quotient][ssa-rewrite] [Observational isomorphism][ssa-obs] |
| LambdaRTL | The acyclic model interprets unary applications in a monad; its alphabet institution takes the observation relation as a parameter. It distinguishes lexical SSA, projected RTL and full RTL store observations. The separate machine RTL adapter reports stuckness as an undefined outcome. | A top region needs a chosen store/label observation order and a typed result and continuation interface. Its interpretation must dominate all observations for every environment at the selected boundary. An instruction relabelling or a lawful monad supplies no such law. [Syntax and model][rtl] [Institution][rtl-inst] [Machine RTL outcomes][rtl-beh] |

An effect bound of `⊤` permits all effects in the typing system. It does
not establish that any computation is greatest. The effect used for a fresh
primitive remains a parameter, and assigning the pure effect would also
invoke existing purity obligations. For a
behaviour-set model one can ask for the existing convention exemplified by
MIR's `ubClose_of_undefined`, which yields the universal outcome set.
Neither the monadic model interfaces nor weak interaction-tree equivalence
provide that UB order or its sequencing laws. [Effect system][effects]
[Empty elimination][quant-typing] [MIR UB closure][mir] [Kleisli model][kleisli]
[Weak-tree semantics][weak-tree]

## Checks

```sh
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Regression
lake build --wfail +Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Refinement.Regression
```

[ordered]: ../../Silmaril/Raw/SSA/Isotope/Institution/Refinement/Ordered.lean
[obs]: ../../Silmaril/Raw/SSA/Isotope/Institution/Observational/Basic.lean
[compiler]: compiles-to.md
[primitive]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Primitive/Thms.lean
[instr]: ../../Silmaril/Raw/SSA/Isotope/Institution/InstrSig.lean
[sigmap]: ../../Silmaril/Raw/SSA/Isotope/Morphism/Instructions/Signature.lean
[syntax]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Syntax/Defs.lean
[signature]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Thms.lean
[spec]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/Specification/Thms.lean
[institution]: ../../Silmaril/Logic/Institution/Theory.lean
[models]: ../../Silmaril/Raw/SSA/Isotope/Logic/Metatheory/Theory/OrderedModel.lean
[case-typing]: ../../Silmaril/Raw/SSA/Isotope/LetCase/LocallyNameless/Typing.lean
[ssa-syntax]: ../../Silmaril/SSA/Isotope/LambdaSSA/Defs.lean
[case-refinement]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Refinement/Thms.lean
[case-model]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Model/Thms.lean
[case-regression]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Refinement/Regression.lean
[case]: ../../Silmaril/SSA/Isotope/Institution/UndefinedBehaviour/LetCase/Thms.lean
[let-theory]: ../../Silmaril/Raw/SSA/Isotope/Institution/Refinement/Isotope.lean
[quant-typing]: ../../Silmaril/Raw/SSA/Isotope/Refinement/Typing.lean
[quant]: ../../Silmaril/SSA/Isotope/Refinement/Thms.lean
[iter-beh]: ../../Silmaril/Raw/SSA/Isotope/LetIter/Semantics/Behaviour.lean
[ssa-typing]: ../../Silmaril/SSA/Isotope/LambdaSSA/Typing/Defs.lean
[ssa-rewrite]: ../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Syntactic/Defs.lean
[ssa-obs]: ../../Silmaril/Raw/SSA/Isotope/Institution/Observational/Isomorphism.lean
[rtl]: ../../Silmaril/SSA/LambdaRTL/Defs.lean
[rtl-inst]: ../../Silmaril/SSA/LambdaRTL/Institution/Defs.lean
[rtl-beh]: ../../Silmaril/Raw/Machine/RTL/Behaviour.lean
[effects]: ../../Silmaril/Raw/SSA/Isotope/Refinement/Effects.lean
[mir]: ../../Silmaril/Raw/Compiler/Mir/Semantics.lean
[kleisli]: ../../Silmaril/SSA/Isotope/LetIter/Categorical/Kleisli/Thms.lean
[weak-tree]: ../../tests/ssa/LetIterWeakTreeSoundness.lean
