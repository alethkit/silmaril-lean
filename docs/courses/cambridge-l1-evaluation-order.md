# Cambridge L1 host interpreter checks

## Exercise 11 evaluation order

Exercise 11 asks how ordinary OCaml or Moscow ML evaluates operators and
sequences, and how that compares with an L1 implementation and the official
L1 rules. Silmaril ships the Lean rules and proofs. Cambridge publishes the
OCaml, Moscow ML and Java companion interpreters as external sources.
Appendices A–C of the pinned notes also list the companion code.
[Exercise 11, p. 31](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=31) ·
[Official materials](https://www.cl.cam.ac.uk/teaching/2526/Semantics/materials.html)

### Check the two levels

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

### Native host observations and guarantees

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

## Exercise 6 machine integers

Exercise 6 asks to fix the L1 semantics to match the implementation,
paying attention to integer representation. The collected L1 rules use
mathematical integers. In Lean, `L1.Exercises.Machine.Step.add` and
`Step.ge` use addition on `BitVec w` and compare the signed `toInt`
values. `reduceConfig` implements these operations. The checked
`overflow_step`, `overflow_interpreter`, `overflow_signed_value` and
`signed_comparison` are four-bit examples. [Exercise 6, p. 31](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=31) ·
[Lean machine integers](../../Silmaril/Courses/Cambridge/L1/Exercises/MachineIntegers.lean)

The command above also runs the `EX6` probes. The OCaml companion
stores integers as `int` in `Integer` and delegates `Plus` and `GTEQ` to
OCaml `+` and `>=`. The Java companion stores `int` in `Int.value`
and delegates `Plus` and `GTeq` to Java `+` and `>=`. The drivers
construct L1 ASTs with representable boundary values and call the
original stepping functions. They also run the same arithmetic and
comparison directly in each host. [OCaml source](https://www.cl.cam.ac.uk/teaching/2526/Semantics/L1/l1_ocaml.ml) ·
[Java source](https://www.cl.cam.ac.uk/teaching/2526/Semantics/L1/l1.java)

These are the signed limits reported by the same Debian 13 x86-64
toolchains listed above. For each row, both the companion and the direct
host operations returned the minimum for `max + 1` and the maximum for
`min + (-1)`, with no overflow exception. They returned `false` for
`(max + 1) >= 0` and `true` for `0 >= (max + 1)`. The Python runner
checks the limits and both sets of results against the expected values
computed independently of the host programs.

| Toolchain | Measured integer width | Minimum | Maximum |
| --- | --- | --- | --- |
| OCaml 5.3.0 (`ocamlc` and `ocamlopt`) | 63 | `-4611686018427387904` | `4611686018427387903` |
| OpenJDK 21.0.13.1 | 32 | `-2147483648` | `2147483647` |

OCaml 5.3 documents `Sys.int_size` as 31 on 32-bit platforms and 63
on 64-bit platforms, with other implementations potentially differing.
The standard library specifies arithmetic modulo `2^Sys.int_size`
without overflow failures and gives `>=` the usual order on signed
integers. [OCaml width](https://ocaml.org/manual/5.3/api/Sys.html#VALint_size) ·
[Integer arithmetic](https://ocaml.org/manual/5.3/api/Stdlib.html#1_Integerarithmetic) ·
[Ordering](https://ocaml.org/manual/5.3/api/Stdlib.html#VAL%28%3E%3D%29)

Java specifies signed 32-bit two's-complement `int`, including on this
64-bit JVM. Integer addition returns the low 32 bits when it overflows,
and `>=` compares the resulting signed values.
[JLS §4.2.1](https://docs.oracle.com/javase/specs/jls/se21/html/jls-4.html#jls-4.2.1) ·
[§4.2.2](https://docs.oracle.com/javase/specs/jls/se21/html/jls-4.html#jls-4.2.2) ·
[§15.18.2](https://docs.oracle.com/javase/specs/jls/se21/html/jls-15.html#jls-15.18.2) ·
[§15.20.1](https://docs.oracle.com/javase/specs/jls/se21/html/jls-15.html#jls-15.20.1)

The runs cover arithmetic and comparison on L1 ASTs for these two
companions. Moscow ML, 31-bit OCaml, other runtimes, and textual parsing
of out-of-range literals were untested. Correspondence between Lean
and the companion interpreters is empirical for these cases.
