module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped

open Functions

/-- The escaping wrapper can bind additional required positional parameters.
Its own lexical block includes the locals assigned after child installation. -/
structure Spec where
  wrapper : Escape.Spec
  assignments : List (String × Lowering.Resolve.SourceExpr)
  additional : List String := []
  updates : List (String × Int) := []

@[expose] def Spec.child (spec : Spec) : Defaults.Body.Definition :=
  ⟨spec.wrapper.childName, spec.wrapper.child.parameters,
    spec.assignments.foldr (fun (name, rhs) rest => .assign name rhs rest)
      (.ret (.scalar (.read spec.wrapper.returned)))⟩

@[expose] def Spec.parameters (spec : Spec) : List String := spec.wrapper.parameter :: spec.additional

@[expose] def Spec.enclosing (spec : Spec) : List String := spec.parameters ++ spec.wrapper.locals spec.updates

@[expose] def Spec.frame (spec : Spec) (childId : Nat) : Forwarding.Frame :=
  spec.wrapper.frame childId spec.additional spec.updates

@[expose] def Spec.command (spec : Spec) : Command :=
  spec.wrapper.commandWith spec.child.body.source spec.additional spec.updates

theorem Spec.capture_owned (spec : Spec) (name : String) (member : name ∈ spec.parameters ++ spec.updates.map Prod.fst) :
    name ∈ spec.enclosing :=
  (List.mem_append.mp member).elim (List.mem_append_left _)
    (fun localName => List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_eraseDups.mpr localName)))

structure Names (spec : Spec) : Prop where
  wrapper : Escape.WrapperNames spec.wrapper
  childFresh : spec.wrapper.childName ∉ spec.additional
  localUpdates : ∀ name ∈ spec.updates.map Prod.fst, name ∉ spec.parameters ∧ name ≠ spec.wrapper.childName
  defaultReads : spec.wrapper.DefaultReads spec.enclosing

/-- The independent body relation determines the entire capture order.
The wrapper profile permits parameter and update-local captures. -/
structure Plan (globals : List String) (spec : Spec) where
  body : Defaults.Body.Plan globals spec.child spec.enclosing
  captured : ∀ entry ∈ body.free, ∃ name ∈ spec.parameters ++ spec.updates.map Prod.fst, entry = ⟨fileSlot name, fileSlot name⟩

structure Admitted (globals : List String) (spec : Spec) : Prop where
  names : Names spec
  plan : Nonempty (Plan globals spec)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped
