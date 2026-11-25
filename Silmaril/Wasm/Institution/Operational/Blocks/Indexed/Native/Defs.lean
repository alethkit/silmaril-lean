module

public import Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Defs
public import Silmaril.Wasm.Institution.Operational.Blocks.Context.Defs
public import Silmaril.Wasm.Institution.Operational.Locals.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Indexed

open Execution
open Execution.Runtime (Frame Value)

def Body.instructions {I : Type} (emit : Locals.Op → I) (branch ret : I) : Body → List I
  | .locals code => code.map emit
  | .branch => [branch]
  | .return_ => [ret]

def State.frame (site : Site) (state : State) : Frame :=
  let locals := match state with
    | .source locals .. | .branch locals _ | .return_ locals _ | .done locals _ | .pendingReturn locals _ => locals
    | .label body => body.locals
  ⟨locals, site.declaration.module⟩

structure Syntax (A : Type) where
  values : List Value → List A
  flat : Locals.Codec A
  block : TypeIdx → Body → A
  label : Nat → List A → A
  branch : A
  ret : A

/-- The saved prefix stays outside the block label, including when a return
crosses it. The enclosing frame will do the final return-value cut. -/
def State.code {A : Type} (ops : Syntax A) (site : Site) (state : State) : List A :=
  ops.values site.saved ++
    match state with
    | .source _ args body => ops.values args ++ [ops.block site.index body]
    | .label body => [ops.label site.signature.results.length (ops.flat.encode body.code)]
    | .branch _ stack => [ops.label site.signature.results.length (ops.values stack ++ [ops.branch])]
    | .return_ _ stack => [ops.label site.signature.results.length (ops.values stack ++ [ops.ret])]
    | .done _ results => ops.values results
    | .pendingReturn _ stack => ops.values stack ++ [ops.ret]

def coreSyntax : Syntax Core.Admin where
  values := Blocks.Context.coreValues
  flat := Locals.coreCodec
  block i body := .plain (.block (.typeIdx i) (body.instructions Locals.coreInstr (.br ⟨0⟩) .return_))
  label n := .label n []
  branch := .plain (.br ⟨0⟩)
  ret := .plain .return_

def limeSyntax : Syntax Wasm.Lime1.Execution.Admin where
  values := Wasm.Lime1.Execution.values
  flat := Locals.limeCodec
  block i body := .source (.block (.typeIdx i) (body.instructions Locals.limeInstr (.br ⟨0⟩) .return_))
  label n := .label n []
  branch := .source (.br ⟨0⟩)
  ret := .source .return_

def coreConfig {H : Type} (s : Core.Store H) (site : Site) (state : State) : Core.Config H :=
  ⟨s, (state.frame site).toCore, state.code coreSyntax site⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (site : Site) (state : State) :
    Wasm.Lime1.Execution.Config H :=
  ⟨s, state.frame site, state.code limeSyntax site⟩

end Silmaril.Wasm.Institution.Operational.Blocks.Indexed
