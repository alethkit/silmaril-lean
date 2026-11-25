# Cambridge L1 Exercise 11 evaluation order

Exercise 11 asks how ordinary OCaml or Moscow ML evaluates operators and
sequences, and how that compares with an L1 implementation and the official
L1 rules. Silmaril ships the Lean rules and proofs. Cambridge publishes the
OCaml, Moscow ML and Java companion interpreters as external sources.
Appendices A–C of the pinned notes also list the companion code.
[Exercise 11, p. 31](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=31) ·
[Official materials](https://www.cl.cam.ac.uk/teaching/2526/Semantics/materials.html)

## Check the two levels

Run from the repository root with Python 3, `ocamlc`, `ocamlopt`, and a JDK
providing `java` and `javac`. On Debian 13 the packages are `python3`,
`ca-certificates`, `ocaml`, and `openjdk-21-jdk-headless`.

```sh
python3 -I tests/courses/cambridge-l1-order/check.py
```

The check downloads the official OCaml and Java sources over HTTPS, verifies
their pinned SHA-256 hashes, and compiles the original bytes with small
drivers in a temporary directory. The Java file is saved as `L1.java` to
match its public class name. Both drivers call the original small-step
functions and check configurations separately from expressions evaluated by
the host language. The Moscow ML source was inspected for the L1 order.
The executable check covers OCaml and Java. [Harness](../../tests/courses/cambridge-l1-order/check.py) ·
[OCaml source](https://www.cl.cam.ac.uk/teaching/2526/Semantics/L1/l1_ocaml.ml) ·
[Java source](https://www.cl.cam.ac.uk/teaching/2526/Semantics/L1/l1.java) ·
[Moscow ML source](https://www.cl.cam.ac.uk/teaching/2526/Semantics/L1/l1.ml)

The L1 cases start with `l = 0`. Each binary operand writes its marker
to `l` and returns zero. The drivers require the full store history
`0,1,1,2,2,2` and final values `0` for addition and `true` for comparison.
Sequencing two assignments must give store history `0,1,1,2` and return
`skip`. The addition and sequencing cases reproduce the Lean fixtures
`L1.Exercises.original_operator_order_trace` and
`L1.Exercises.sequence_left_first_trace`. The comparison case uses the
same operand rules. In all three companion sources the interpreter
chooses one operand reduction based on whether the first operand is
a value, and only drops the first command of a sequence once it is
`skip`. [Lean fixtures](../../Silmaril/Courses/Cambridge/L1/Exercises/EvaluationOrder.lean) ·
[L1 reduction rules](../../Silmaril/Courses/Cambridge/L1/Reduction.lean) ·
[Collected L1 definition, pp. 29–30](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=29)

## Native host observations and guarantees

Each host expression also calls marker functions directly, with `1` for
the left operand and `2` for the right. These are the results on Debian
13 x86-64 with OCaml package `5.3.0-3` and OpenJDK
`21.0.13.1+2-1~deb13u1`. The runner prints the tools used.

| Running the probes | L1 interpreter writes | Host `+` and `>=` markers | Host sequence markers |
| --- | --- | --- | --- |
| OCaml 5.3.0 bytecode (`ocamlc`) | `1,2` | `2,1` | `1,2` |
| OCaml 5.3.0 native (`ocamlopt`) | `1,2` | `2,1` | `1,2` |
| OpenJDK 21.0.13.1 (`javac` and `java`) | `1,2` | `1,2` | `1,2` |

OCaml treats ordinary infix operators such as `+` and `>=` as function
applications and leaves their argument evaluation order unspecified.
The observed right-before-left order is specific to the compiler modes
and version above. The check accepts either order for those host operators.
For `e1; e2`, the manual specifies that OCaml evaluates `e1` before `e2`.
[OCaml operators](https://ocaml.org/manual/5.3/expr.html#ss:expr-operators) ·
[Function application](https://ocaml.org/manual/5.3/expr.html#sss:expr-functions-application) ·
[Sequence](https://ocaml.org/manual/5.3/expr.html#sss:expr-sequence)

Java specifies left-before-right evaluation of binary operands and
first-to-last execution of statements within a block. The fixture checks
both guarantees. The interpreter trace checks the rules of L1, even on a
host like OCaml whose ordinary operators can evaluate in a different order.
[JLS §15.7.1](https://docs.oracle.com/javase/specs/jls/se21/html/jls-15.html#jls-15.7.1) ·
[JLS §14.2](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.2)

The same drivers could document the Exercise 6 integer boundary with
a separate maximum-plus-one case, recording `Sys.int_size` for OCaml
and the Java `int` limit. The order fixtures use small integers.
Exercise 6's width-parametric Lean proofs therefore keep their existing
scope. [Lean machine integers](../../Silmaril/Courses/Cambridge/L1/Exercises/MachineIntegers.lean)
