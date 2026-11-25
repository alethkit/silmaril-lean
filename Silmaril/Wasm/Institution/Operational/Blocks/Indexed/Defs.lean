module

public import Silmaril.Wasm.Institution.Operational.Locals.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Declaration.Defs
public import Silmaril.Wasm.Lime1.Types

/-!
# Checked indexed blocks in an entered frame

The bounded body is either flat local code with normal fallthrough or an
immediate depth-zero branch or function return. The static descriptor fixes
the current module and its resolved numeric signature. Operands below the
block arguments remain outside the label.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Indexed

open Execution.Runtime (Value)

/-- The enclosing function declaration supplies the actual frame module, the
local types and the separate function return types. -/
structure Site where
  declaration : CallContinuation.OuterCall.Declaration
  index : TypeIdx
  signature : Wasm.Lime1.FuncType
  saved : List Value

def Site.Resolved (site : Site) : Prop :=
  site.declaration.module.types[site.index.toNat]? = some site.signature

instance (site : Site) : Decidable site.Resolved :=
  inferInstanceAs (Decidable (_ = _))

def Site.localTypes (site : Site) : List NumType :=
  site.declaration.params ++ site.declaration.locals

inductive Body where
  | locals (code : List Locals.Op)
  | branch
  | return_

def SuffixTyped (types : List NumType) (stack : List Value) : Prop :=
  (stack.map Value.type).reverse.take types.length = types.reverse

def Body.check (site : Site) : Body → Bool
  | .locals code =>
      decide (Locals.check site.localTypes site.signature.params.reverse code = some site.signature.results.reverse)
  | .branch =>
      decide (site.signature.params.reverse.take site.signature.results.length = site.signature.results.reverse)
  | .return_ =>
      decide (site.signature.params.reverse.take site.declaration.results.length = site.declaration.results.reverse)

def Site.checkSource (site : Site) (locals args : List Value) (body : Body) : Bool :=
  decide site.Resolved && decide (locals.map Value.type = site.localTypes) &&
    decide (args.map Value.type = site.signature.params) && body.check site

inductive State where
  | source (locals args : List Value) (body : Body)
  | label (body : Locals.State)
  | branch (locals stack : List Value)
  | return_ (locals stack : List Value)
  | done (locals results : List Value)
  /-- The block is gone. The enclosing function still owns this return. -/
  | pendingReturn (locals stack : List Value)

def Body.entered (locals args : List Value) : Body → State
  | .locals code => .label ⟨locals, Locals.values args ++ code⟩
  | .branch => .branch locals args
  | .return_ => .return_ locals args

def State.Typed (site : Site) : State → Prop
  | .source locals args body =>
      locals.map Value.type = site.localTypes ∧ args.map Value.type = site.signature.params ∧ body.check site = true
  | .label a => Locals.Admitted site.localTypes site.signature.results.reverse a
  | .branch locals stack =>
      locals.map Value.type = site.localTypes ∧ SuffixTyped site.signature.results stack
  | .return_ locals stack | .pendingReturn locals stack =>
      locals.map Value.type = site.localTypes ∧ SuffixTyped site.declaration.results stack
  | .done locals results => locals.map Value.type = site.localTypes ∧ results.map Value.type = site.signature.results

def Admitted (site : Site) (state : State) : Prop :=
  site.Resolved ∧ state.Typed site

/-- Source entry and the three label exits are independent of native steps.
Flat local body steps use the existing local SOS. -/
inductive Edge (site : Site) : State → State → Prop where
  | enter (locals args : List Value) (body : Body) :
      Edge site (.source locals args body) (body.entered locals args)
  | reduce {a b : Locals.State} (move : Locals.Edge a b) :
      Edge site (.label a) (.label b)
  | fallthrough (locals results : List Value) :
      Edge site (.label ⟨locals, Locals.values results⟩) (.done locals results)
  | branch (locals scratch results : List Value) (arity : results.length = site.signature.results.length) :
      Edge site (.branch locals (scratch ++ results)) (.done locals results)
  | return_ (locals stack : List Value) :
      Edge site (.return_ locals stack) (.pendingReturn locals stack)

abbrev Runs (site : Site) := Relation.ReflTransGen (Edge site)

end Silmaril.Wasm.Institution.Operational.Blocks.Indexed
