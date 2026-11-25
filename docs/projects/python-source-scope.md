# Python source syntax and function scope

Use [Source.Syntax.Defs](../../Silmaril/Languages/Python/Source/Syntax/Defs.lean)
for unresolved constructor data and
[Source.Scope.Thms](../../Silmaril/Languages/Python/Source/Scope/Thms.lean)
for executable analysis and its enclosing-binder law. The source fragment
covers modules, classes, nested functions and lambdas with positional
parameters and defaults, assignment and deletion targets, declarations,
selective imports, and conditional, loop and exception suites.

`analyze` collects name occurrences and declarations before resolving each
block. A name assigned later in a function is local throughout that block.
A default expression is read in the block defining the function.
Nested functions refer to captured names by stable paths. Each defining
function reports its cells, and intervening functions report the captures
they forward. The module and explicit global declarations are enclosing
lookup barriers. An unbound `nonlocal`, a declaration following a use or
binding, and a parameter/declaration collision produce distinct diagnostics.

Class bases are read in the enclosing block. Class bodies distinguish
namespace lookup from free access to an enclosing cell. Method lookup skips
the ordinary class namespace, including its global declarations, while
functions referring to the synthetic `__class__` cell capture their enclosing
class. A use of `super` within a function adds the implicit `__class__` use.

Lambda bodies have function scope and leave the enclosing namespace
untouched. Defaults, decorators and class bases introduce any lambdas in
the enclosing block. Child paths follow traversal order. Function defaults
precede function decorators, and class decorators precede bases.

Destructuring and loop targets bind their names in the current block.
Attribute and subscript targets read their operands. Exception-handler
targets and selective import aliases also bind in the current block.
Star imports report an explicit diagnostic because their bindings would
depend on a runtime module.

Expression syntax retains collections, comparison chains, slices, yield
operands and call argument forms. Text literals carry code points, including
lone surrogates. Floating literals carry binary64 bits. Scope visits all
dictionary keys before values. The constructor profile reports unsupported
comprehensions, generator expressions and bytes literals explicitly.

`enclosingBinding_eq_some_iff` characterizes successful executable lookup
with an inductive nearest-binder judgment. `enclosingBinding_stops`
characterizes lookup at a barrier. The regression exercises the full
constructor-to-scope path, including shadowing, forwarding through a function
with no direct use, default scope, and rejected declarations.

The scope profile follows Python 3.7 lexical binding and declaration rules.
Deleting a name counts as binding it for scope analysis. This entry point
accepts constructor data and checks the represented scope rules. Text parsing,
full syntax validation, compilation, and runtime name
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
- Python 3.7.17, §3.3.3.6, SHA-256
  `e67c556ea43d2660d174ccaa64e122483170da92dc84512b0837fd163c01dd0b`.
  [Creating the class object](https://docs.python.org/release/3.7.17/reference/datamodel.html#creating-the-class-object)
- Python 3.7.17, §6.14, SHA-256
  `53021dbaf574df1726e3eb15dba1915b8dd7c2c4e06a26bf1782bddd13cb15bd`.
  [Lambdas](https://docs.python.org/release/3.7.17/reference/expressions.html#lambdas)
