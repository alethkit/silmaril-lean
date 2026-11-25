module

public import Silmaril.Logic.Temporal.TLA.DataElab.Semantics

/-! Prepare a first-order instance invocation in its captured host frame. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Instances.Replay

open Resolution

public section

/-- Expanded expression bindings for one instantiation of a module. -/
abbrev Frame (signature : ExternalSignature) (fragment : Fragment) :=
  List (BindingId × Term signature fragment)

inductive DiagnosticKind where
  | missingBinding (id : BindingId)
  | operatorReplacement (id : BindingId)
  | invalidArity (id : BindingId)
  deriving DecidableEq, Repr

structure Diagnostic where
  site : Site
  kind : DiagnosticKind
  deriving DecidableEq, Repr

structure Invocation (signature : ExternalSignature) (fragment : Fragment) where
  home : Binding
  frame : Frame signature fragment
  arguments : List (Term signature fragment)

/-- Interpret all replacements in the incoming host frame with the instance
formals. Only the finished substitutions enter the child frame. -/
def prepare {signature : ExternalSignature} {fragment : Fragment} {m : Type → Type} [Monad m]
    (registry : CheckedRegistry) (site : Site) (plan : InstancePlan) (member : InstanceMember)
    (args : List (Term signature fragment)) (fail : {α : Type} → Diagnostic → m α)
    (visit : Frame signature fragment → Site → Surface.Expr → m (Term signature fragment))
    (invoke : Frame signature fragment → Site → Binding → m (Term signature fragment)) :
    m (Invocation signature fragment) := do
  let some home := registry.findBinding member.home
    | fail ⟨site, .missingBinding member.home⟩
  unless args.length = plan.parameters.length + home.slots.length do
    fail ⟨site, .invalidArity member.id⟩
  let formals := plan.parameters.zip (args.take plan.parameters.length)
  let frame ← plan.substitutions.mapM fun (id, replacement) => do
    let origin := match replacement with
      | .expression origin _ => origin
      | .binding _ => plan.site
    let some target := registry.findBinding id
      | fail ⟨origin, .missingBinding id⟩
    unless target.slots.isEmpty do
      fail ⟨origin, .operatorReplacement id⟩
    let term ← match replacement with
      | .expression rhsSite body => visit formals rhsSite body
      | .binding replacementId => do
        let some binding := registry.findBinding replacementId
          | fail ⟨origin, .missingBinding replacementId⟩
        unless binding.slots.isEmpty do
          fail ⟨origin, .operatorReplacement replacementId⟩
        invoke formals origin binding
    return (id, term)
  return ⟨home, frame, args.drop plan.parameters.length⟩

end

end Silmaril.Logic.Temporal.TLA.DataElab.Instances.Replay
