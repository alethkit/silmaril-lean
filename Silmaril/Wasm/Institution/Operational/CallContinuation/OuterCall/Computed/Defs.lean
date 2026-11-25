module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Defs
public import Silmaril.Wasm.Numerics.Integer

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Execution.Runtime (FuncAddr Value ModuleInst Frame)

/-- A single integer argument computed by reading two initialized outer locals
and applying one typed integer binary operation. The bits are lookup witnesses
in the native guard and do not occur in the outer function's source code. -/
structure Site where
  outerIndex : FuncIdx
  outerAddr : FuncAddr
  innerAddr : FuncAddr
  args : List Value
  outerModule : ModuleInst
  typeIndex : TypeIdx
  params : List NumType
  locals : List NumType
  innerIndex : FuncIdx
  inner : CallFrame.Callee
  kind : IntType
  leftIndex : LocalIdx
  rightIndex : LocalIdx
  op : IntBinOp
  left : BitVec kind.width
  right : BitVec kind.width

def Site.arity (site : Site) := site.inner.arity

def Site.frame (site : Site) : Frame :=
  ⟨site.args ++ site.locals.map Value.zero, site.outerModule⟩

structure Typed (site : Site) : Prop where
  outerArgs : site.args.map Value.type = site.params
  leftLookup : site.frame.locals[site.leftIndex.toNat]? = some (.int site.kind site.left)
  rightLookup : site.frame.locals[site.rightIndex.toNat]? = some (.int site.kind site.right)
  innerParams : site.inner.params = [.int site.kind]
  innerBody : site.inner.program.Typed site.inner
  nonRecursive : site.outerAddr ≠ site.innerAddr

inductive State (site : Site) where
  | call
  | invoke
  | readLeft
  | readRight
  | compute
  | argument (bits : BitVec site.kind.width)
  | argumentTrap
  | nested (phase : Nested.State)

def Site.innerStart (site : Site) (bits : BitVec site.kind.width) : Nested.State :=
  .label (.active (.invoke [] [.int site.kind bits]))

def Admitted (site : Site) : State site → Prop
  | .nested phase => Nested.Admitted site.inner phase
  | _ => True

inductive Ground (site : Site) : State site → State site → Prop where
  | resolve : Ground site .call .invoke
  | enter : Ground site .invoke .readLeft
  | readLeft : Ground site .readLeft .readRight
  | readRight : Ground site .readRight .compute
  | compute {bits : BitVec site.kind.width}
      (ok : Numerics.intBinOp site.kind site.op site.left site.right = .ok bits) :
      Ground site .compute (.argument bits)
  | trap {cause : Numerics.IntTrap}
      (error : Numerics.intBinOp site.kind site.op site.left site.right = .error cause) :
      Ground site .compute .argumentTrap
  | dropCall : Ground site .argumentTrap (.nested (.label (.trapped [] true)))
  | dropCallAndNop : Ground site .argumentTrap (.nested (.label (.trapped [] false)))
  | resolveInner (bits : BitVec site.kind.width) :
      Ground site (.argument bits) (.nested (site.innerStart bits))

inductive Judgment (site : Site) where
  | nested (edge : Nested.Judgment)
  | step (a b : State site)

inductive RuleInstance (site : Site) : Rule (Judgment site) → Prop where
  | inherit {r : Rule Nested.Judgment} (rule : Nested.RuleInstance site.inner site.arity r) :
      RuleInstance site ⟨r.premises.map .nested, .nested r.conclusion⟩
  | delegate (a b : Nested.State) :
      RuleInstance site ⟨[.nested (.step a b)], .step (.nested a) (.nested b)⟩
  | ground {a b : State site} (rule : Ground site a b) : RuleInstance site ⟨[], .step a b⟩

def shape (site : Site) : SOS.Shape.{0} :=
  ⟨⟨State site, Unit⟩, Judgment site, fun (a, _, b) => .step a b⟩

def presentation (site : Site) : SOS.Presentation := ⟨shape site, {r | RuleInstance site r}⟩

abbrev Edge (site : Site) (a b : State site) := (presentation site).Derives (.step a b)
abbrev Runs (site : Site) := Relation.ReflTransGen (Edge site)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed
