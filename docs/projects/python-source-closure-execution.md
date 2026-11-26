# Executing fixed positional Python closures from source

The [source runner](../../Silmaril/Languages/Python/Compile/Closure/Run/Thms.lean)
links the analyzed source to the Core closure executor. Each value is an
integer literal or a name read. A nested function definition stores a
closure with the linked code reference and ordered captures. A positional
call assigns its result to a named local or cell. Each function has a
final value return or falls through to an implicit `None` return. Source
lowering erases a `pass` before either exit. It consumes no Core steps and
preserves the frame layout and lexical child order. Fallthrough emits
the existing executor return with a literal `None` operand. A nested
call writes that value to its destination before resuming the caller.
Bare `return` and explicit `None` syntax remain outside this source profile.

A standalone zero-argument call to a resolved name uses the executor's
discard destination. The caller resumes with its saved frame and the
callee's residual heap. The call preserves the lexical child index.
For these statements the compiler requires an empty argument list and a
bare name callee. The module-function runner also allows resolved global
reads, which use the current module binding at invocation.

A final `return local(...)` uses the checked ordinary local callee and
the existing positional operand checker. The executor reads the callee
and operands before invocation. Successful normal call delivery writes
the result to that same private local and returns it. The local is
outside the shared cell heap, so the reuse preserves owned and captured
cells and does not allocate a frame slot. Defined errors and faults use
the existing saved-caller delivery path.

A final `return global_name(...)` in a module function reads the live
global before evaluating its checked positional operands. It uses the
same dispatch and saves the caller frame. Success resumes that frame
and forwards the value with the reached heap without writing a local or
cell. A defined error propagates through the existing saved-caller rule.
Shared-cell callees require a separate final-call rule.

A module can bind a lambda with required, fixed positional parameters.
The plan checks the lambda's analyzed function block and the declared
parameter order, then publishes it with the existing code-table path.
A body can return a nested lambda directly. Its lexical child row
uses the same parameter destinations and capture layout as a named
function. The return constructs the descriptor from the current owned
and forwarded cells. It delivers that descriptor and the same heap
before any call to the child's body. Entry allocates the child's owned
cells and initializes its checked parameter destinations.

The checked profile covers terminal lambda chains whose leaf is an
existing checked return expression. Default expressions, variadic and
keyword-only signatures, and non-terminal lambda calls require their own
checks. The seeded factory runner uses its same-run descriptor
ledger and the same positional and receipt rules for returned lambdas.
The controls check that repeated calls share forwarded cells where
expected and allocate distinct owned cells even with equal arguments.
[Lowering and return theorems](../../Silmaril/Languages/Python/Compile/Closure/Run/Thms.lean)
[Entry and capture theorems](../../Silmaril/Languages/Python/Compile/Closure/Call/Thms.lean)

A terminal call to a lambda expression can also return the child's result.
The same linked child reference supplies the callee descriptor from the
parent's frame. The executor evaluates the checked positional operands
from left to right, binds them in the child, and forwards the exact
result and reached heap without a local store. A failed operand read
keeps the incoming heap and prevents child entry. The seeded factory
selector follows the lexical reference within its existing two-wrapper
bound, with at most one positional operand at that internal call.
The outer module call settles one receipt for the returned descriptor.
[Entry, argument failure and forwarding theorems](../../Silmaril/Languages/Python/Compile/Closure/Run/Thms.lean)

Message-free body assertions lower to the existing executor assertion
when the test passes the ordinary runner operand check. They preserve
the continuation's lexical child paths and code keys. The executor
continues on truth and uses ordinary defined error delivery on failure.
The assertion operand profile covers Boolean literals, integer literals,
resolved reads, checked integer arithmetic, and a single comparison of the form `name == integer_literal`.
This comparison requires the exact integer AST node and reuses the ordinary
name resolver for locals, cells and, in the module-function runner, globals.
Core reads the name once, preserving lookup errors, then compares exact
integers and treats Booleans as 0 or 1. The modeled `None` and function values
compare unequal to an integer. Calls, chained comparisons and
user-defined equality are outside this profile. In a module invocation, a
failed body assertion is raised as `AssertionError`.

The ordinary body profile also accepts message-free literal-string membership
and non-membership assertions against `name.__code__.co_freevars`. The linker
attaches the sorted names of the checked lexical captures, including forwarded
captures, to the layout-matched code definition. The executor compares the
literal code points with that tuple after reading the current name. An alias
uses the same code reference and cells. This metadata profile covers ordinary
function paths with distinct ASCII capture identifiers and excludes class paths
and synthetic `super` and `__class__` captures. A nonfunction receiver or
unprofiled definition gives a distinct executor fault. The source profile
admits the tuple lookup inside these assertions.

The `co_cellvars` source form accepts message-free literal-string
non-membership on a resolved bare name. Its code definition records the
sorted names of the checked function's owned cells. Forwarded captures still
contribute to `co_freevars`. A definition with captured parameters has no
`co_cellvars` tuple in this profile because their observable ordering differs
between CPython 3.7 and 3.13. The executor retains the literal code points and
uses the same frame, heap and function identity through the test.
The source and linker also recognize message-free
`assert "<literal>" in name.__code__.co_names` in an ordinary function.
The name-table evidence is indexed by the linked code key and layout. It
models the order in which CPython 3.7.3 and 3.13.5 intern name operands
in `exec` mode at optimization level zero. It records global loads,
the two attribute loads of this form, and the assertion-failure operation.
The 3.7.3 tuple includes the synthetic `AssertionError` name. The 3.13.5
tuple uses a dedicated opcode for that branch. Repeated names keep their
first index, and each nested body has its own table. Unsupported code
shapes have no checked tuple. The linker attaches the exact 3.13.5 tuple
and its profile tag to the checked definition. The ordinary executor
reads the current function and its code key once, preserves the exact
literal code points, and uses the existing assertion failure path. The
3.7.3 tuple remains available as source evidence.

The function-aware module plan recognizes a separate message-free
`assert "<literal>" in name.__code__.co_varnames` form. It retains one
resolved module-name read at that point in the plan and preserves the
literal's code points. Fast-local tuple evidence follows checked local
loads and stores in emission order, including the store of a nested
definition into its parent. Each nested body has a separate tuple.
This evidence covers CPython 3.13.5 in `exec` mode at optimization level
zero for the checked straight-line profile with at most one fixed
positional parameter, no defaults or parameter annotations, and no
owned cells or incoming captures. The verified parameter prefix
includes an unread parameter. Later fast locals keep their first
emission order with parameter names and repeats removed. The module
runner reads the current binding once and resolves that function's
code key and layout. It
checks exact code-point membership without invoking the function.
A profiled empty tuple gives a false assertion. Missing metadata and
non-function receivers give distinct module profile stops. An unbound
name raises `NameError`, and invalid code references keep their
dispatch faults. The instruction preserves earlier bindings and heap
effects and skips the tail on failure. The seeded runner uses the same
tuple evaluator after one module-first lookup. The namespace, heap and
earlier call receipts are preserved, and the metadata instruction emits
no receipt. Unprofiled tuples and unsupported receiver values stop in
the seeded unsupported profile.

Successful lowering retains the source translation and preserves the
definition, layout and parameter destinations at every emitted code key.
Body lowering succeeds exactly when the independent translation judgment
has a derivation.
The entry starts with a fresh heap and binds the supplied arguments by
position. The runner produces the actual labelled Core path, with an
explicit state at the fuel limit.

The conformance check feeds Python source files through AST intake and
compilation and checks the resulting Core execution against CPython. It
covers a forwarded nonlocal write observed by the original caller,
arity and noncallable errors, and an unbound capture propagated out of the
callee. It also checks a live one-step prefix and the diagnostic for
arithmetic in an executor body.

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.Closure.Run.Thms
```
