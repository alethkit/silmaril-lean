module

public import Silmaril.Languages.Starlark.Modules.Loader.Defs
public import Silmaril.Languages.Starlark.Functions.Operational.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Loader

open Functions (Program Exec)
open Lists (Outcome)

/-- Big-step rules for demand-driven initialization and load statements. -/
inductive Runs (program : Program) (manifest : Manifest) :
    {α : Type} → List ModuleId → Job α → Session → Result α → Prop where
  | cycle {active : List ModuleId} {id : ModuleId} {s : Session} :
      id ∈ active →
      Runs program manifest active (.initialize id) s (.error (.cycle (active.reverse ++ [id])) s)
  | cached {active : List ModuleId} {id : ModuleId} {s : Session} {published : Published} :
      id ∉ active → s.cache.lookup id = some published →
      Runs program manifest active (.initialize id) s (.ok published s)
  | unknownModule {active : List ModuleId} {id : ModuleId} {s : Session} :
      id ∉ active → s.cache.lookup id = none → ¬ id < manifest.size →
      Runs program manifest active (.initialize id) s (.error (.unknownModule id) s)
  | reject {active : List ModuleId} {id : ModuleId} {s : Session} {error : Modules.Error}
      (bound : id < manifest.size) :
      id ∉ active → s.cache.lookup id = none →
      validateSource program manifest[id].source = .error error →
      Runs program manifest active (.initialize id) s (.error (.initialization id error) s)
  | initialize {active : List ModuleId} {id : ModuleId} {s : Session} {out : Result Unit}
      (bound : id < manifest.size) :
      id ∉ active → s.cache.lookup id = none →
      validateSource program manifest[id].source = .ok () →
      Runs program manifest (id :: active) (.commands id manifest[id].source.commands)
        { s with runtime := enter manifest[id].source s.runtime } out →
      Runs program manifest active (.initialize id) s (finish id manifest[id].source s.runtime out)
  | exec {active : List ModuleId} {requester : ModuleId} {code : TopCode} {s : Session}
      {out : Outcome Lists.Iteration.Flow} :
      Exec program (List.range program.size) s.runtime code.body out →
      Runs program manifest active (.command requester (.exec code)) s
        (liftResult requester s (afterCode out))
  | missingLabel {active : List ModuleId} {requester : ModuleId} {label : String}
      {imports : List Import} {s : Session} :
      resolve manifest requester label = none →
      Runs program manifest active (.command requester (.load label imports)) s
        (.error (.missingLabel requester label) s)
  | loadFailed {active : List ModuleId} {requester id : ModuleId} {label : String}
      {imports : List Import} {s t : Session} {error : Error} :
      resolve manifest requester label = some id →
      Runs program manifest active (.initialize id) s (.error error t) →
      Runs program manifest active (.command requester (.load label imports)) s (.error error t)
  | load {active : List ModuleId} {requester id : ModuleId} {label : String}
      {imports : List Import} {s t : Session} {published : Published} :
      resolve manifest requester label = some id →
      Runs program manifest active (.initialize id) s (.ok published t) →
      Runs program manifest active (.command requester (.load label imports)) s
        (liftResult requester t (bindImports (importsOf published label imports) t.runtime))
  | done {active : List ModuleId} {requester : ModuleId} {s : Session} :
      Runs program manifest active (.commands requester []) s (.ok () s)
  | step {active : List ModuleId} {requester : ModuleId} {first : Command} {rest : List Command}
      {s t : Session} {out : Result Unit} :
      Runs program manifest active (.command requester first) s (.ok () t) →
      Runs program manifest active (.commands requester rest) t out →
      Runs program manifest active (.commands requester (first :: rest)) s out
  | failed {active : List ModuleId} {requester : ModuleId} {first : Command} {rest : List Command}
      {s t : Session} {error : Error} :
      Runs program manifest active (.command requester first) s (.error error t) →
      Runs program manifest active (.commands requester (first :: rest)) s (.error error t)

end Silmaril.Languages.Starlark.Modules.Loader
