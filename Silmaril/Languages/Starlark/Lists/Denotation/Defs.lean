module

public import Silmaril.Languages.Starlark.Lists.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists

/-- Compose the effects in source evaluation order, retaining the state at
the first dynamic error. -/
def denote {α : Type} : Code α → Meaning α
  | .scalar value => pure (.scalar value)
  | .read ref => fun state => state.read ref
  | .list elements => do
    allocate (← denote elements)
  | .empty => pure []
  | .cons head tail => do
    let value ← denote head
    return value :: (← denote tail)
  | .index receiver index => do
    let value ← denote receiver
    readIndex value (← denote index)
  | .append receiver argument => do
    match ← denote receiver with
    | .scalar _ => throw .appendTarget
    | .list address => appendAt address (← denote argument)
  | .pass => pure ()
  | .eval expr => do
    let _ ← denote expr
    return ()
  | .assign binding rhs => do
    bindValue binding (← denote rhs)
  | .setIndex receiver index rhs => do
    let value ← denote rhs
    let target ← denote receiver
    writeIndex target (← denote index) value
  | .seq first rest => do
    denote first
    denote rest

end Silmaril.Languages.Starlark.Lists
