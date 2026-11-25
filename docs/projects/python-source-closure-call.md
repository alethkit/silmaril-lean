# Entering a lowered Python closure

The [call adapter](../../Silmaril/Languages/Python/Compile/Closure/Call/Defs.lean)
takes an analyzed parent and child layout, the caller's frame and typed
continuation, and the evaluated positional argument values. The checked
child layout provides each target parameter destination and capture
operand. The adapter uses the Core closure and call entry operations.

The [correspondence laws](../../Silmaril/Languages/Python/Compile/Closure/Call/Thms.lean)
give successful entry when the argument count matches the source
declaration and every selected parent cell is allocated. At each declared
position, the argument reads back from the bounded destination bearing
the source parameter name. Incoming captures keep the selected parent
identities and their pre-entry contents. Finishing delivers a value or a
defined error to the original caller with the residual shared heap.

The regression supplies positional values to a function with an owned
parameter, an ordinary local parameter, and an incoming capture. It checks
the reads after entry, the arity diagnostic, and the saved caller's read of
a changed captured cell after both kinds of finish. The calling machine
supplies code-table lookup, body evaluation and continuation dispatch.

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.Closure.Call.Thms
```
