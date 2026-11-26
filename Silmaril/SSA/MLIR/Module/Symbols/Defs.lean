module

public import Silmaril.SSA.MLIR.Module.Defs

/-! # Function symbols and direct calls in one flat module -/

@[expose] public section

namespace Silmaril.MLIR

universe u v w

/-- The declared input and result interfaces of a function. -/
structure FuncSignature (I : Type u) (O : Type v) where
  inputs : I
  outputs : O
  deriving DecidableEq

variable {I : Type u} {O : Type v} {B : I → O → Type w}

/-- Read the declared interfaces independently of the definition's body. -/
def FuncOf.signature (fn : FuncOf B) : FuncSignature I O :=
  ⟨fn.inputs, fn.outputs⟩

/-- Project the ordered module to its unique symbols and declared signatures. -/
def FuncModule.signatures (mod : FuncModule B) : Module (FuncSignature I O) :=
  Module.map FuncOf.signature mod

/-- Evidence that a flat `func.call` symbol has exactly the requested interfaces.
The evidence depends only on the module's signatures. -/
structure DirectCall (symbols : Module (FuncSignature I O)) (inputs : I) (outputs : O) where
  callee : String
  resolved : symbols.find? callee = some ⟨inputs, outputs⟩

/-- Admit a direct call by looking up its symbol in the whole module and checking both interfaces. -/
def DirectCall.resolve? [DecidableEq I] [DecidableEq O] (symbols : Module (FuncSignature I O))
    (callee : String) (inputs : I) (outputs : O) : Option (DirectCall symbols inputs outputs) :=
  if found : symbols.find? callee = some ⟨inputs, outputs⟩ then
    some ⟨callee, found⟩
  else none

end Silmaril.MLIR
