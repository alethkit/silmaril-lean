module

import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Thms
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs

namespace Silmaril.Languages.Starlark.Functions.Lowering

private def localName (name : String) : Binding := ⟨.local, name⟩
private def events : Binding := ⟨.global, "events"⟩
private def functionName : Binding := ⟨.global, "body"⟩
private def marker : Binding := localName "marker"

private def read (name : Binding) : Lists.Expr := .read (.bound name)
private def integer (value : Int) : Lists.Expr := .scalar (.int value)

private def program : Program :=
  let result := localName "result"
  let effects := ["a", "b", "c"].map fun parameter =>
    Body.total (.atomic (.eval (.append (read events) (read (localName parameter)))))
  let finish := Body.seq
    (.call (some result) (.builtin .len) { positional := [read (localName "d")] })
    (.total (.ret (read result)))
  #[⟨{ positional := ["a", "b", "c", "d"].map fun name => ⟨localName name, none⟩ },
    [result], [⟨events, events⟩], effects.foldr Body.seq finish⟩]

private def setup : Body :=
  .seq (.total (.atomic (.assign events (.list .empty)))) (.define functionName 0)

private def invoke (last : Lists.Expr) : Expr :=
  .call (.atom (read functionName)) [.atom (integer 1)] [("c", .atom (integer 3))]
    (some (.atom (.tuple (operandList [integer 2]))))
    (some (.atom (.dict (.entry .noEntries (.string "d") last))))

private def execute (last : Lists.Expr) : Lists.Outcome Lists.Value :=
  let root := (({} : Lists.State).allocateSlot events).write marker (.scalar (.int 7))
  Lists.Outcome.resume (run program setup root) fun _ => denoteExpr program [0] (invoke last)

private def effectsAndCaller (state : Lists.State) : Bool :=
  decide (state.bindings marker = some (.scalar (.int 7)) ∧
    state.slots events = some (.owned 0) ∧ state.slots (localName "result") = none) &&
  match state.bindingValue events with
  | .ok (.list address) =>
    match Lists.listElements address state with
    | .ok [.scalar (.int 1), .scalar (.int 2), .scalar (.int 3)] _ => true
    | _ => false
  | _ => false

-- Both calls reach the core body and its inner built-in. Only its built-in argument differs.
#guard
  match execute (read events) with
  | .ok (.scalar (.int 3)) final => effectsAndCaller final
  | _ => false

#guard
  match execute (integer 9) with
  | .error (.builtinType .len (.scalar (.int 9))) final => effectsAndCaller final
  | _ => false

end Silmaril.Languages.Starlark.Functions.Lowering
