module

import Silmaril.Languages.Starlark.Functions.Thms
import Silmaril.Languages.Starlark.Modules.Thms
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Syntax.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs
meta import Silmaril.Languages.Starlark.Modules.Defs

namespace Silmaril.Languages.Starlark.Functions

private def localName (name : String) : Binding := ⟨.local, name⟩
private def globalName (name : String) : Binding := ⟨.global, name⟩
private def events := globalName "events"
private def record := globalName "record"
private def factory := globalName "factory"
private def functionName := globalName "f"
private def seed := localName "seed"
private def xs := localName "xs"
private def stamp := localName "stamp"

private def read (binding : Binding) : Lists.Expr := .read (.bound binding)
private def int (n : Int) : Lists.Expr := .scalar (.int n)
private def set (binding : Binding) (value : Lists.Expr) : Body :=
  .total (.atomic (.assign binding value))
private def append (binding : Binding) (value : Lists.Expr) : Body :=
  .total (.atomic (.eval (.append (read binding) value)))
private def ret (expr : Lists.Expr) : Body := .returnExpr (.atom expr)

private def note (marker result : Lists.Expr) : Lowering.Expr :=
  .callPos (.atom (read record)) [.atom marker, .atom result]

private def program (bad : Bool) : Program :=
  let marker := localName "marker"
  let result := localName "result"
  let inner := localName "inner"
  let second := if bad then Lowering.Expr.callPos (.atom (.builtin .len)) [note (int 2) (int 9)]
    else note (int 2) (int 2)
  let later : List Parameter := if bad then [⟨localName "later", some (note (int 3) (int 3))⟩] else []
  #[
    ⟨{ positional := [⟨marker, none⟩, ⟨result, none⟩] }, [], [⟨events, events⟩],
      .seq (append events (read marker)) (ret (read result))⟩,
    ⟨{ positional := [⟨seed, none⟩] }, [inner], [⟨record, record⟩],
      .seq (.define inner 2) (ret (read inner))⟩,
    ⟨{ positional := [⟨xs, some (note (read seed) (.list .empty))⟩],
        keywordOnly := ⟨stamp, some second⟩ :: later },
      [], [], .seq (append xs (read stamp)) (ret (read xs))⟩
  ]

private def setup : List Body :=
  [set events (.list .empty), .define record 0, .define factory 1]

private def initial : Lists.State :=
  [events, record].foldl Lists.State.allocateSlot {}

private def makeFunction : Body :=
  .call (some functionName) (read factory) { positional := [int 1] }

private def hasList (state : Lists.State) (address : Lists.Address) (expected : List Int) : Bool :=
  match Lists.listElements address state with
  | .ok values _ => decide (values = expected.map fun n => .scalar (.int n))
  | _ => false

private def hasEvents (state : Lists.State) (expected : List Int) : Bool :=
  match state.bindingValue events with
  | .ok (.list address) => hasList state address expected
  | _ => false

-- The positional default sees the defining activation's seed. Both calls reuse the same stored list.
#guard
  let a := globalName "a"
  let b := globalName "b"
  let code := (setup ++ [makeFunction, .call (some a) (read functionName) {}]).foldr Body.seq
    (.call (some b) (read functionName) {})
  match runChecked (program false) code initial with
  | .ok (.ok .next final) =>
    match final.bindingValue a, final.bindingValue b, final.bindingValue functionName with
    | .ok (.list first), .ok (.list second), .ok (.function address) =>
      match getClosure address final with
      | .ok closure _ =>
        first == second && hasList final first [2, 2] && hasEvents final [1, 2] &&
          decide (closure.defaults = [(xs, .list first), (stamp, .scalar (.int 2))])
      | _ => false
    | _, _, _ => false
  | _ => false

-- A failing default keeps earlier effects and allocations, skips the later default and preserves the old binding.
#guard
  let code := setup.foldr Body.seq (.define functionName 2)
  let start := (initial.write seed (.scalar (.int 1))).write functionName (.scalar (.int 7))
  match runChecked (program true) code start with
  | .ok (.error (.builtinType .len (.scalar (.int 9))) final) =>
    hasEvents final [1, 2] &&
      final.heap.any (fun cell => match cell.contents with
        | .list [] => true
        | _ => false) &&
      final.heap.all (fun cell => match cell.contents with
        | .function closure => closure.declaration != 2
        | _ => true) &&
      match final.bindingValue functionName with
      | .ok (.scalar (.int 7)) => true
      | _ => false
  | _ => false

-- The checked runner validates default syntax even in an unused declaration.
#guard
  let invalid := Lowering.Expr.call (.atom (.builtin .len)) []
    [("x", .atom (int 1)), ("x", .atom (int 2))] none none
  let default := Lowering.Expr.logical .or (.atom (int 1)) invalid
  let declarations : Program := #[⟨{ positional := [⟨xs, some default⟩] },
    [], [], ret (int 0)⟩]
  match runChecked declarations (.total (.atomic .pass)) with
  | .error (.duplicateExplicitKeyword "x") => true
  | _ => false

-- A default runs under the defining activation's available declarations.
#guard
  let maker := globalName "maker"
  let inner := localName "inner"
  let default := Lowering.Expr.callPos (.atom (read maker)) []
  let declarations : Program := #[
    ⟨{}, [inner], [⟨maker, maker⟩], .seq (.define inner 1) (ret (read inner))⟩,
    ⟨{ positional := [⟨xs, some default⟩] }, [], [], ret (read xs)⟩]
  let code := Body.seq (.define maker 0) (.call none (read maker) {})
  match runChecked declarations code (({} : Lists.State).allocateSlot maker) with
  | .ok (.error (.recursiveCall 0) _) => true
  | _ => false

-- The returned function is the only route from module globals to its stored default list.
#guard
  let provider : Modules.Source := ⟨["events", "record", "factory", "f"], [], [
    .exec (.atomic (.assign events (.list .empty))), .exec (.define "record" 0),
    .exec (.define "factory" 1),
    .exec (.call (some functionName) (read factory) { positional := [int 1] })]⟩
  let consumer : Modules.Source := ⟨[], [], [.load "provider" [⟨"f", "use"⟩],
    .exec (.call none (read (Modules.fileSlot "use")) {})]⟩
  match Modules.initializeModule (program false) (fun _ => none) provider {} with
  | .ok published state =>
    match List.lookup "f" published.exports with
    | some (.function address) =>
      match getClosure address state with
      | .ok closure _ =>
        match List.lookup xs closure.defaults with
        | some (.list root) =>
          match Modules.initializeModule (program false)
              (fun label => if label = "provider" then some published else none) consumer state with
          | .error (.runtime (.frozen rejected)) _ => rejected == root
          | _ => false
        | _ => false
      | _ => false
    | _ => false
  | _ => false

end Silmaril.Languages.Starlark.Functions
