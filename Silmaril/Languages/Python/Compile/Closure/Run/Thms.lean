module

public import Silmaril.Languages.Python.Compile.Closure.Run.Defs
public import Silmaril.Languages.Python.Core.Closure.Executor.Thms
import Silmaril.Proofs.Languages.Python.Compile.Closure.Run.Correspondence

public section
namespace Silmaril.Languages.Python.Compile.Closure.Run

open Core.Closure (CodeRef Layout Value)
open Core.Closure.Dispatch (Definition resolve)
open Core.Closure.Executor (Event State labelled runPrefix)

theorem lower_complete {layout : Layout} {source : Link.Code layout}
    {target : Core.Closure.Executor.Body layout} (translated : Translation source target) :
    lowerCode source = some ⟨target, translated⟩ :=
  Proofs.Languages.Python.Compile.Closure.Run.lower_complete translated

theorem lower_rejected_iff {layout : Layout} (source : Link.Code layout) :
    lowerCode source = none ↔ ¬∃ target, Translation source target :=
  Proofs.Languages.Python.Compile.Closure.Run.lower_rejected_iff source

theorem Compiled.resolve_entry {source : Source.Module} (compiled : Compiled source) :
    ∃ target : Core.Closure.Executor.Body compiled.entry.layout,
      Translation (Link.linkBody 1 compiled.sourceBody.moduleTree compiled.sourceBody.code).code target ∧
      resolve compiled.table compiled.entry = .ok
        { parameters := compiled.sourceBody.parameters
          body := target
          freevars := (Link.link compiled.sourceBody).entryFreeVars
          cellvars := (Link.link compiled.sourceBody).entryCellVars
          codeNames := (Link.link compiled.sourceBody).entryCodeNames } :=
  Proofs.Languages.Python.Compile.Closure.Run.resolve_entry compiled

theorem Compiled.resolve_reference {source : Source.Module} (compiled : Compiled source)
    {path : Source.BlockPath} {ref : CodeRef}
    (emitted : (path, ref) ∈ (Link.link compiled.sourceBody).references) :
    ∃ (definition : Definition Link.Code ref.layout) (target : Core.Closure.Executor.Body ref.layout),
      resolve (Link.link compiled.sourceBody).table ref = .ok definition ∧
      Translation definition.body target ∧
      resolve compiled.table ref = .ok
        { parameters := definition.parameters
          body := target
          freevars := definition.freevars
          cellvars := definition.cellvars
          codeNames := definition.codeNames
          varnames := definition.varnames } :=
  Proofs.Languages.Python.Compile.Closure.Run.resolve_reference compiled emitted

theorem run_path {source : Source.Module} {compiled : Compiled source} {arguments : List Value}
    {fuel : Nat} {initial residual : State} {events : List Event}
    (started : start compiled arguments = .ok initial)
    (observed : run compiled arguments fuel = .ok (events, residual)) :
    (labelled compiled.table).Path initial events residual := by
  have exactRun : runPrefix compiled.table fuel initial = (events, residual) := by
    simpa [run, started] using observed
  simpa only [exactRun] using Core.Closure.Executor.run_path compiled.table fuel initial

/-- Returning a newly created closure reads only the current frame to
build its descriptor. The next state delivers that descriptor and the same heap. -/
theorem returnClosure_delivers {layout : Layout} (table : Core.Closure.Executor.CodeTable)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Core.Closure.Heap)
    (frame : Core.Closure.Frame layout) (ref : CodeRef)
    (captures : Fin ref.layout.captures → Core.Closure.CaptureSlot layout)
    (stack : Core.Closure.Executor.Stack) :
    Core.Closure.Executor.StepIn table globals (.running heap frame (.ret (.closure ref captures)) stack)
      none (.delivering heap stack (.ok (.function (frame.closure ref captures)))) :=
  .ret (.closure ref captures)

/-- After successful call delivery, the returned value occupies the
private local and the remaining body returns that value. -/
theorem returnedLocalCall_resume {layout : Layout} (heap : Core.Closure.Heap)
    (frame : Core.Closure.Frame layout) (slot : Fin layout.locals) (value : Value)
    (stack : Core.Closure.Executor.Stack) :
    Core.Closure.Executor.resumeStore heap frame (.local slot) value (.ret (.read (.local slot))) stack =
      (none, .running heap
        { frame with locals := fun query => if query = slot then some value else frame.locals query }
        (.ret (.read (.local slot))) stack) := rfl

end Silmaril.Languages.Python.Compile.Closure.Run
