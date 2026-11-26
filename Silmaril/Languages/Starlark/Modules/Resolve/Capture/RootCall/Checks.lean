module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall

open scoped Functions.Lowering.Quote

open Block (ModuleBinders)

private def chain : Forwarding.Chain :=
  .mixed "apply" ["i"] ⟨"first", starlark%[box], starlark%[i], .plain starlark%[pair], starlark%[box[i]]⟩

private def root : Command := .define chain.name (.required chain.parameters) chain.body

private def setup : List Command :=
  [.assign "box" starlark%[[3]], .assign "pair" starlark%[(0, 9)], .assign "indices" starlark%[[0]]]

private def unrelated : Command := .define "other" (.required ["a", "b"]) (.ret (some starlark%[100]))

private def commands : List Command := setup ++
  [root, .assign "alias" starlark%[apply], .eval starlark%[apply(indices[0])], unrelated,
    .assign "out" starlark%[box[0]]]

private def linked : Functions.Program :=
  #[⟨requiredSignature [], [], [], .returnExpr (.atom (.scalar (.int 777)))⟩]

-- The code slot is shifted by the linked program. A later unrelated
-- declaration preserves that slot. Copying the closure to another global
-- does not disturb the original binding.
#guard
  match resolve commands linked, runModule commands (fun _ => none) {} linked with
  | .ok resolved, .ok (.ok published _) =>
    match resolved.source.commands[3]?, resolved.source.commands[6]?,
      published.exports.lookup "apply", published.exports.lookup "alias" with
    | some (Modules.Command.exec (.define "apply" id)), some (Modules.Command.exec (.define "other" later)), some fn, some copied =>
      id == 1 && later == 2 && resolved.program.size == 3 && fn == copied &&
        published.exports.lookup "out" == some (.scalar (.int 9))
    | _, _, _, _ => false
  | _, _ => false

private def zero : Command := .assign "later" starlark%[0]
private def empty : Command := .assign "empty" starlark%[[]]

-- A reached callee read error wins over a reached-first-argument candidate.
#guard
  match runModule (setup ++ [.eval starlark%[apply(later)], root, zero]) (fun _ => none) {} with
  | .ok (.error (.runtime (.uninitialized name)) _) => name == globalSlot "apply"
  | _ => false

-- Either first argument wins over the other and over surplus arity.
#guard
  match runModule (setup ++ [root, empty, .eval starlark%[apply(empty[0], later)], zero]) (fun _ => none) {} with
  | .ok (.error (.runtime (.indexRange 0 0)) _) => true
  | _ => false

#guard
  match runModule (setup ++ [root, empty, .eval starlark%[apply(later, empty[0])], zero]) (fun _ => none) {} with
  | .ok (.error (.runtime (.uninitialized name)) _) => name == globalSlot "later"
  | _ => false

#guard
  match runModule (setup ++ [root, .eval starlark%[apply(0, 1)]]) (fun _ => none) {} with
  | .ok (.error (.runtime (.arity 1 2)) _) => true
  | _ => false

private def call : List Command := [.eval starlark%[f(7)], .assign "f" starlark%[9]]

example {resolved : ResolvedModule} (checked : resolve call = .ok resolved) :
    resolved.source.commands[0]? =
      some (.exec (.evalExpr (.call (.atom (.read (.bound (globalSlot "f")))) [.atom (.scalar (.int 7))] [] none none))) :=
  checked_call_site [] _ _ _ _ _ ["f"] #[] resolved (.cons (.eval _) (.cons (.assign ..) .nil)) checked
    (.global (by decide) (.global (by simp) (by simp) (by simp))) (.cons (.int 7) .nil)

private def linkedRoot : List Command := setup ++
  [root, .assign "alias" starlark%[apply], .eval starlark%[apply(indices[0])]]

example {resolved : ResolvedModule} (checked : resolve linkedRoot linked = .ok resolved)
    (accepted : ∀ program, Forwarding.Accepted ["box", "pair", "indices", "apply", "alias"] program [] chain) :
    ∃ id, resolved.source.commands[3]? = some (.exec (.define "apply" id)) ∧
      ∃ declaration, resolved.program[id]? = some declaration := by
  have binders : ModuleBinders linkedRoot ["box", "pair", "indices", "apply", "alias"] :=
    .cons (.assign ..) (.cons (.assign ..) (.cons (.assign ..)
      (.cons (.define ..) (.cons (.assign ..) (.cons (.eval _) .nil)))))
  obtain ⟨head, _, id, _, emitted, found⟩ := checked_root_site setup _ chain _ linked resolved binders checked
    accepted (.assign _ _ (.eval _ .nil))
  exact ⟨id, emitted, head.declaration, found⟩

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall
