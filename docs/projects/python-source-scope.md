# Python source syntax and function scope

Use [Source.Syntax.Defs](../../Silmaril/Languages/Python/Source/Syntax/Defs.lean)
for unresolved constructor data and
[Source.Scope.Thms](../../Silmaril/Languages/Python/Source/Scope/Thms.lean)
for executable analysis and its enclosing-binder law. The source fragment
covers modules, nested functions with positional parameters and defaults,
name assignment and deletion, declarations, and conditional and loop suites.

`analyze` collects name occurrences and declarations before resolving each
block. A name assigned later in a function is local throughout that block.
A default expression is read in the block defining the function.
Nested functions refer to captured names by stable paths. Each defining
function reports its cells, and intervening functions report the captures
they forward. The module and explicit global declarations are enclosing
lookup barriers. An unbound `nonlocal`, a declaration following a use or
binding, and a parameter/declaration collision produce distinct diagnostics.

`enclosingBinding_eq_some_iff` characterizes successful executable lookup
with an inductive nearest-binder judgment. `enclosingBinding_stops`
characterizes lookup at a barrier. The regression exercises the full
constructor-to-scope path, including shadowing, forwarding through a function
with no direct use, default scope, and rejected declarations.

The scope profile follows Python 3.7 lexical binding and declaration rules.
Deleting a name counts as binding it for scope analysis. This entry point
accepts constructor data and checks the represented scope rules. Text parsing,
full syntax validation, class and lambda scopes, compilation, and runtime name
lookup are later boundaries.

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Source.Scope.Thms
```

- Python 3.7.17, §4.2, SHA-256
  `2fff14c12f27e67e029528cdb3c2de6f0c499759d7ce33584731f50f5daffada`.
  [Execution model](https://docs.python.org/release/3.7.17/reference/executionmodel.html#naming-and-binding)
- Python 3.7.17, §§7.12–7.13, SHA-256
  `3cb18a48cde43c0df94f8e52522cf7fe0a56cdd15b463dea1009cedf8794147c`.
  [Simple statements](https://docs.python.org/release/3.7.17/reference/simple_stmts.html#the-global-statement)
