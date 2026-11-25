module

import Silmaril.Languages.Starlark.Modules.Resolve.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve

open scoped Functions.Lowering.Quote

private def noImports : Catalog := fun _ => none

private def closures : List Command := [
  .assign "value" starlark%["global"],
  .define "outer" { positional := [⟨"value", none⟩] }
    (.seq (.define "middle" {}
        (.seq (.define "inner" { positional := [⟨"value", some starlark%[value]⟩] }
            (.ret (some starlark%[value if ready else "wrong"])))
          (.ret (some starlark%[inner]))))
      (.seq (.assign "value" starlark%["updated"]) (.ret (some starlark%[middle])))),
  .assign "middle" starlark%[outer("initial")],
  .assign "inner" starlark%[middle()],
  .assign "ready" starlark%[True],
  .eval starlark%[inner()],
  .assign "out" starlark%[inner()],
  .assign "explicit" starlark%[inner(value = "caller")]]

-- The inner parameter and its default's defining-scope read share a name.
-- Only the intervening function needs to capture the outer local for that default.
#guard
  match resolve closures with
  | .ok resolved =>
    match resolved.program[0]?, resolved.program[1]?, resolved.program[2]? with
    | some inner, some middle, some outer =>
      let sources := fun declaration : Functions.Declaration => declaration.free.map Functions.FreeName.source
      resolved.source.globals == ["value", "outer", "middle", "inner", "ready", "out", "explicit"] &&
      sources inner == [globalSlot "ready"] &&
      sources middle == [fileSlot "value", globalSlot "ready"] &&
      sources outer == [globalSlot "ready"] && outer.locals == [fileSlot "middle"] &&
      match inner.signature.positional with
      | [⟨parameter, some (.atom (.read (.bound read)))⟩] =>
        parameter == fileSlot "value" && read == fileSlot "value"
      | _ => false
    | _, _, _ => false
  | _ => false

#guard
  match runModule closures noImports {} with
  | .ok (.ok published _) =>
    decide (published.exports.lookup "out" = some (.string "updated")) &&
      decide (published.exports.lookup "explicit" = some (.string "caller"))
  | _ => false

-- Forward lexical references are legal. Evaluation before their binding is dynamic.
#guard
  let commands := [.assign "out" starlark%[len("x")], .assign "len" starlark%[1]]
  match runModule commands noImports {} with
  | .ok (.error (.runtime (.uninitialized slot)) _) => slot == globalSlot "len"
  | _ => false

#guard
  let commands := [.assign "x" starlark%[8], .define "f" {}
      (.seq (.branch starlark%[False] (.assign "x" starlark%[1]) .pass) (.ret (some starlark%[x]))),
    .assign "out" starlark%[f()]]
  match runModule commands noImports {} with
  | .ok (.error (.runtime (.uninitialized slot)) _) => slot == fileSlot "x"
  | _ => false

#guard
  let commands := [.define "f" { positional := [⟨"other", some starlark%[other]⟩] } .pass,
    .assign "other" starlark%[1], .eval starlark%[f()]]
  match runModule commands noImports {} with
  | .ok (.error (.runtime (.uninitialized slot)) state) =>
    slot == globalSlot "other" && state.heap.size == 2
  | _ => false

#guard
  let commands := [.define "f" {} (.branch starlark%[False] (.eval starlark%[missing()]) .pass)]
  match runModule commands noImports {} with
  | .error (.expression (.lexical (.undefinedName "missing"))) => true
  | _ => false

private def importValue : Command := .load "dep" [⟨"provided", "imported"⟩]

#guard
  match runModule [.assign "out" starlark%[imported], importValue] noImports {} with
  | .ok (.error (.runtime (.uninitialized slot)) _) => slot == fileSlot "imported"
  | _ => false

-- A closure can capture the file alias before its load populates the slot.
#guard
  let commands := [.define "f" {} (.ret (some starlark%[imported])), importValue,
    .assign "out" starlark%[f()]]
  match runModule [.assign "provided" starlark%[7]] noImports {} with
  | .ok (.ok dep state) =>
    match runModule commands (fun label => if label == "dep" then some dep else none) state with
    | .ok (.ok published _) =>
      decide (published.exports.lookup "out" = some (.scalar (.int 7))) &&
        (published.exports.lookup "imported").isNone
    | _ => false
  | _ => false

-- Appending the consumer's declarations preserves the IDs in imported closure values.
#guard
  let provider : List Command := [.define "provided" {} (.ret (some starlark%[value])),
    .assign "value" starlark%[7]]
  let consumer : List Command := [importValue, .assign "value" starlark%[99],
    .define "use" {} (.ret (some starlark%[imported()])), .assign "out" starlark%[use()]]
  match resolve provider with
  | .ok resolved =>
    match initializeModule resolved.program noImports resolved.source {} with
    | .ok dep state =>
      match runModule consumer (fun _ => some dep) state resolved.program with
      | .ok (.ok published _) => decide (published.exports.lookup "out" = some (.scalar (.int 7)))
      | _ => false
    | _ => false
  | _ => false

-- The pinned spec disallows both load/global collision orders.
#guard
  let rejected := fun commands => match resolve commands with
    | .error (.validation (.bindingCollision "imported")) => true
    | _ => false
  let assign : Command := .assign "imported" starlark%[1]
  rejected [importValue, assign] && rejected [assign, importValue]

#guard
  match resolve [.assign "a" starlark%[1], .define "a" {} .pass] with
  | .error (.validation (.bindingCollision "a")) => true
  | _ => false

#guard
  match resolve [.define "f" { positional := [⟨"x", none⟩, ⟨"x", none⟩] } .pass] with
  | .error (.validation (.syntax (.duplicateParameter "x"))) => true
  | _ => false

#guard
  match resolve [.load "dep" []] with
  | .error (.emptyLoad "dep") => true
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve
