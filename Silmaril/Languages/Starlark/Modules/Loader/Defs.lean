module

public import Silmaril.Languages.Starlark.Modules.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Modules.Loader

open Functions (Program)
open Lists (State)

abbrev ModuleId := Nat

structure Entry where
  source : Source
  labels : List (String × ModuleId) := []

/-- Array indices are canonical module IDs. Each entry resolves its own labels. -/
abbrev Manifest := Array Entry

def resolve (manifest : Manifest) (requester : ModuleId) (label : String) : Option ModuleId :=
  manifest[requester]?.bind fun entry => List.lookup label entry.labels

/-- Reuse a session only with the same manifest and linked declaration table. -/
structure Session where
  runtime : State := {}
  cache : List (ModuleId × Published) := []

inductive Error where
  | missingLabel (requester : ModuleId) (label : String)
  | unknownModule (id : ModuleId)
  | cycle (path : List ModuleId)
  | initialization (id : ModuleId) (error : Modules.Error)
  deriving DecidableEq, Repr

abbrev Result := EStateM.Result Error Session

inductive Job : Type → Type where
  | initialize (id : ModuleId) : Job Published
  | command (requester : ModuleId) (command : Command) : Job Unit
  | commands (requester : ModuleId) (commands : List Command) : Job Unit

def Job.weight {α : Type} : Job α → Nat
  | .initialize _ => 0
  | .command .. => 1
  | .commands _ steps => steps.length + 2

/-- The current load chain is innermost first. It is local to a single request. -/
def pending (manifest : Manifest) (active : List ModuleId) : List ModuleId :=
  (List.range manifest.size).filter (fun id => !active.contains id)

theorem pending_length_lt (manifest : Manifest) (active : List ModuleId) (id : ModuleId)
    (bound : id < manifest.size) (fresh : id ∉ active) :
    (pending manifest (id :: active)).length < (pending manifest active).length := by
  rw [show pending manifest (id :: active) =
    (pending manifest active).filter (fun other => !decide (other = id)) by
    simp [pending, List.filter_filter, Bool.not_or]]
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨id, by simp [pending, bound, fresh], by simp⟩

def resume {α β : Type} (result : Result α) (next : α → Session → Result β) : Result β :=
  match result with
  | .ok value state => next value state
  | .error error state => .error error state

def liftResult {α : Type} (id : ModuleId) (session : Session) : Modules.Result α → Result α
  | .ok value runtime => .ok value { session with runtime }
  | .error error runtime => .error (.initialization id error) { session with runtime }

def finish (id : ModuleId) (source : Source) (caller : State) : Result Unit → Result Published
  | .error error session =>
    .error error { session with runtime := restoreThread caller session.runtime }
  | .ok () session =>
    let (published, runtime) := publish source session.runtime
    .ok published ⟨restoreThread caller runtime, (id, published) :: session.cache⟩

/-- Finite descent is measured by inactive manifest entries and remaining
commands. Cycle rejection is a host policy, and evaluation uses no fuel. -/
def denote (program : Program) (manifest : Manifest) (active : List ModuleId)
    {α : Type} (job : Job α) (session : Session) : Result α :=
  match job with
  | .initialize id =>
    if id ∈ active then .error (.cycle (active.reverse ++ [id])) session
    else
      match session.cache.lookup id with
      | some published => .ok published session
      | none =>
        if bound : id < manifest.size then
          let source := manifest[id].source
          match validateSource program source with
          | .error error => .error (.initialization id error) session
          | .ok () =>
            finish id source session.runtime (denote program manifest (id :: active)
              (.commands id source.commands) { session with runtime := enter source session.runtime })
        else .error (.unknownModule id) session
  | .command requester (.exec code) =>
    liftResult requester session (afterCode (Functions.run program code.body session.runtime))
  | .command requester (.load label imports) =>
    match resolve manifest requester label with
    | none => .error (.missingLabel requester label) session
    | some id =>
      resume (denote program manifest active (.initialize id) session) fun published next =>
        liftResult requester next (bindImports (importsOf published label imports) next.runtime)
  | .commands _ [] => .ok () session
  | .commands requester (first :: rest) =>
    resume (denote program manifest active (.command requester first) session) fun () next =>
      denote program manifest active (.commands requester rest) next
termination_by ((pending manifest active).length, job.weight)
decreasing_by
  all_goals first
    | apply Prod.Lex.left; exact pending_length_lt manifest active _ (by assumption) (by assumption)
    | apply Prod.Lex.right; simp [Job.weight]

def load (program : Program) (manifest : Manifest) (id : ModuleId) (session : Session := {}) :
    Result Published :=
  denote program manifest [] (.initialize id) session

end Silmaril.Languages.Starlark.Modules.Loader
