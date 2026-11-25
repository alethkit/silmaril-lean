module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence

open Execution
open Execution.Runtime (Frame)
open StraightLine
open Computed (ArgumentSyntax v1Syntax limeSyntax coreSyntax)
open Computed.Sequence (v1Source limeSource coreSource)

def Site.type (site : Site) : Wasm.V1.FuncType := ⟨site.params, site.result.toList⟩

def Program.body {A : Type} (p : Program) (ops : ArgumentSyntax A) : List A :=
  p.code.map (Sequence.emit ops)

def Program.v1Func (p : Program) : Wasm.V1.Func := ⟨p.site.typeIndex, p.site.locals, p.body v1Source⟩

def Program.limeFunc (p : Program) : Wasm.Lime1.Func := ⟨p.site.typeIndex, p.site.locals, p.body limeSource⟩

def Program.coreFunc (p : Program) : Wasm.Func :=
  ⟨p.site.typeIndex, p.site.locals.map Wasm.V1.ValType.toCore, p.body coreSource⟩

def Program.coreInstance {H : Type} (p : Program) : Core.FuncInst H :=
  ⟨p.site.type.toDefType, p.site.module.toCore, .wasm p.coreFunc⟩

structure Lookups (caller : Frame) (p : Program) : Prop where
  typed : Typed p
  resolves : caller.module.funcs[p.site.index.toNat]? = some p.site.address

structure V1Guard {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (p : Program) : Prop
    extends Lookups caller p where
  allocated : s.funcs[p.site.address.value]? = some (.wasm p.site.type p.site.module p.v1Func)
  body : Sequence.V1Guard s p.site.body

structure LimeGuard {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (p : Program) : Prop
    extends Lookups caller p where
  allocated : s.funcs[p.site.address.value]? = some (.wasm p.site.type p.site.module p.limeFunc)
  body : Sequence.LimeGuard s p.site.body

structure CoreGuard {H : Type} (s : Core.Store H) (caller : Frame) (p : Program) : Prop
    extends Lookups caller p where
  allocated : s.funcs[p.site.address.value]? = some p.coreInstance
  body : Sequence.CoreGuard s p.site.body

def render {A : Type} {site : Site} (call invoke : List A) (label frame : List A → A)
    (body : Sequence.State site.body → List A) (result : Nested.Result → List A) : State site → List A
  | .call => call
  | .invoke => invoke
  | .label state => [frame [label (body state)]]
  | .exit out => [frame (result out)]
  | .done out => result out

def v1Code (site : Site) : State site → List Wasm.V1.Execution.Admin :=
  render (Wasm.V1.Execution.values site.args ++ [.source (.call site.index)])
    (Wasm.V1.Execution.values site.args ++ [.invoke site.address])
    (.label site.arity []) (.frame site.arity site.frame)
    (Sequence.v1Code site.body) (Nested.resultCode Wasm.V1.Execution.values .trap)

def limeCode (site : Site) : State site → List Wasm.Lime1.Execution.Admin :=
  render (Wasm.Lime1.Execution.values site.args ++ [.source (.call site.index)])
    (Wasm.Lime1.Execution.values site.args ++ [.invoke site.address])
    (.label site.arity []) (.frame site.arity site.frame)
    (Sequence.limeCode site.body) (Nested.resultCode Wasm.Lime1.Execution.values .trap)

def coreCode (site : Site) : State site → List Core.Admin :=
  render (coreValues site.args ++ [.plain (.call site.index)])
    (coreValues site.args ++ [.ref (.func site.address.value), .callRefType site.type.toDefType])
    (.label site.arity []) (.frame site.arity site.frame.toCore)
    (Sequence.coreCode site.body) (Nested.resultCode coreValues .trap)

def v1Config {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : Site) (q : State site) :
    Wasm.V1.Execution.Config H := ⟨s, caller, v1Code site q⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (caller : Frame) (site : Site) (q : State site) :
    Wasm.Lime1.Execution.Config H := ⟨s, caller, limeCode site q⟩

def coreConfig {H : Type} (s : Core.Store H) (caller : Frame) (site : Site) (q : State site) :
    Core.Config H := ⟨s, caller.toCore, coreCode site q⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence
