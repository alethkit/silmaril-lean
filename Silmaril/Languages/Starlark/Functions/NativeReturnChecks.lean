module

import Silmaril.Languages.Starlark.Functions.Thms
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Functions.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Syntax.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs

namespace Silmaril.Languages.Starlark.Functions

private def global (name : String) : Binding := ⟨.global, name⟩
private def localName (name : String) : Binding := ⟨.local, name⟩
private def events := global "events"
private def mark := global "mark"
private def pick := global "pick"
private def driver := global "driver"
private def outcome := global "out"

private def read (binding : Binding) : Lists.Expr := .read (.bound binding)
private def int (value : Int) : Lists.Expr := .scalar (.int value)
private def callMark (value : Int) : Lowering.Expr :=
  .callPos (.atom (read mark)) [.atom (int value)]

private def driverValue (bad : Bool) : Lowering.Expr :=
  let keyword := if bad then Lowering.Expr.callPos (.atom (.builtin .len)) [callMark 2] else callMark 2
  let spread := Lists.Code.list (.cons (.append (read events) (int 3)) .empty)
  .call (.atom (read pick)) [callMark 1] [("c", keyword)] (some (.atom spread)) none

private def program (bad : Bool) : Program :=
  let n := localName "n"
  let params := ["a", "b", "c"].map localName
  #[
    ⟨{ positional := [⟨n, none⟩] }, [], [⟨events, events⟩],
      .seq (.total (.atomic (.eval (.append (read events) (read n))))) (.returnExpr (.atom (read n)))⟩,
    ⟨{ positional := params.map fun slot => ⟨slot, none⟩ }, [], [],
      .returnExpr (.atom (.tuple (operandList (params.map read))))⟩,
    ⟨{}, [], [⟨mark, mark⟩, ⟨pick, pick⟩, ⟨events, events⟩], .returnExpr (driverValue bad)⟩
  ]

private def execute (bad : Bool) :=
  let initial := ([events, mark, pick].foldl Lists.State.allocateSlot {}).write outcome (.scalar (.int 7))
  let code := [
    Body.total (.atomic (.assign events (.list .empty))),
    .define mark 0, .define pick 1, .define driver 2
  ].foldr Body.seq (.call (some outcome) (read driver) {})
  runChecked (program bad) code initial

private def hasEvents (state : Lists.State) (expected : List Int) : Bool :=
  match state.bindingValue events with
  | .ok (.list address) =>
    match Lists.listElements address state with
    | .ok values _ => decide (values = expected.map fun n => .scalar (.int n))
    | _ => false
  | _ => false

-- Multiple native returns participate in one call chain. Operands run in source order.
#guard
  match execute false with
  | .ok (.ok .next final) =>
    hasEvents final [1, 2, 3] &&
      match final.bindingValue outcome with
      | .ok (.tuple address) =>
        match Lists.tupleElements address final with
        | .ok [.scalar (.int 1), .scalar .none, .scalar (.int 2)] _ => true
        | _ => false
      | _ => false
  | _ => false

-- A failing keyword operand retains both appends, skips the spread, and leaves the result slot alone.
#guard
  match execute true with
  | .ok (.error (.builtinType .len (.scalar (.int 2))) final) =>
    hasEvents final [1, 2] &&
      match final.bindingValue outcome with
      | .ok (.scalar (.int 7)) => true
      | _ => false
  | _ => false

-- Calling the active declaration from its own return operand rejects re-entry.
#guard
  let self := global "self"
  let value := Lowering.Expr.callPos (.atom (read self)) []
  let recursive : Program := #[⟨{}, [], [⟨self, self⟩], .returnExpr value⟩]
  let code := Body.seq (.define self 0) (.call none (read self) {})
  match runChecked recursive code (({} : Lists.State).allocateSlot self) with
  | .ok (.error (.recursiveCall 0) _) => true
  | _ => false

-- Checked declarations validate calls even in a return operand's skipped branch.
#guard
  let invalid := Lowering.Expr.call (.atom (.builtin .len)) []
    [("x", .atom (int 1)), ("x", .atom (int 2))] none none
  let value := Lowering.Expr.logical .or (.atom (int 1)) invalid
  let declarations : Program := #[⟨{}, [], [], .returnExpr value⟩]
  match runChecked declarations (.total (.atomic .pass)) with
  | .error (.duplicateExplicitKeyword "x") => true
  | _ => false

end Silmaril.Languages.Starlark.Functions
