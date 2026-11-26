module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf.Module

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf

open Functions
open Lists (State Outcome Capture)
open Lists.Iteration (Flow)
open Assignment (LexicalBlock)
open Block (ModuleBinders)

local notation "Value" => Lists.Value

/-- The lexical judgments identify the exact mixed leaf code emitted by the resolver. -/
theorem code_of_lexical {block : LexicalBlock} {body : MixedBody} {plan : Plan}
    {code : Body} (compiled : LeafCode block body code) (lexical : Resolves block body plan) :
    code = plan.code :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf.code_of_lexical compiled lexical

/-- The independent ordered leaf rules determine both resolved execution
and the direct denotation, including all retained state after failure. -/
theorem leaf_sound (program : Program) (available : List DeclarationId) (plan : Plan)
    (state : State) (legal : plan.Legal) (clean : noPrivateSlots state)
    {out : Outcome Flow} (runs : Runs plan state out) :
    Exec program available state plan.code out ∧ denoteBody program available plan.code state = out :=
  let same := Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf.leaf_denotes
    program available plan state legal clean runs
  ⟨(exec_iff_denoteBody _ _ _ _ _).mpr same, same⟩

/-- The wrapper and mixed leaf rules derive the checked body from an
activated call and determine the exact caller-restored outcome. -/
theorem body_sound (program : Program) (available : List DeclarationId) (caller : State)
    (frame : Forwarding.Frame) (captures : List Capture) (assigned : List (Binding × Value))
    {out : Outcome Value} (source : BodyRuns program caller frame captures assigned out) :
    ∃ bodyOut, Exec program available (activate caller frame.declaration captures assigned) frame.code bodyOut ∧
      returnTo caller bodyOut = out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf.body_sound
    program available caller frame captures assigned source

/-- Checked compilation and independent binder collection supply the
first source definition step and its linked declaration table. -/
theorem checked_first_definition (after : List Command) (chain : Forwarding.Chain)
    (globals : List String) (linked : Program) (resolved : ResolvedModule)
    (declared : ModuleBinders (.define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (.define chain.name (.required chain.parameters) chain.body :: after) linked = .ok resolved)
    (accepted : ∀ program, Forwarding.Accepted globals program [] chain)
    (suffix : RootCall.Segment globals after) (caller : State) :
    ∃ seed frame rest next,
      Forwarding.Emits globals [] chain (frame :: rest) ∧
      Forwarding.Links seed chain (frame :: rest) ∧
      Wrapper.KeepsTable seed resolved.program (frame :: rest) ∧
      Step resolved globals 0 (enter resolved.source caller)
        (.define chain.name (.required chain.parameters) chain.body) (.ok () next) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf.checked_first_definition
    after chain globals linked resolved declared checked accepted suffix caller

/-- Starting at actual module entry, a reached trace of the bounded source
rules and its publication or failure observation determine the exact
resolved operational and denotational module results. -/
theorem checked_module {commands : List Command} {globals : List String} {linked : Program}
    {resolved : ResolvedModule} {out : Modules.Result Unit} {published : Modules.Result Modules.Published}
    (declared : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved)
    (host : Modules.Catalog) (caller : State)
    (reached : Wrapper.ReachedPrefix (Step resolved globals) 0 (enter resolved.source caller) commands out)
    (observes : Finishes globals caller out published) :
    Initializes commands host caller linked (.ok published) ∧ runModule commands host caller linked = .ok published :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf.checked_module
    declared checked host caller reached observes

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf
