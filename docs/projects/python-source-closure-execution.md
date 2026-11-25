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

Message-free body assertions lower to the existing executor assertion
when the test passes the ordinary runner operand check. They preserve
the continuation's lexical child paths and code keys. The executor
continues on truth and uses ordinary defined error delivery on failure.
The assertion operand profile covers integer literals and resolved
reads. Computed calls and arithmetic are outside it. In a module
invocation, a failed body assertion is raised as `AssertionError`.

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
