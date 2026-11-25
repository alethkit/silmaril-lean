module

public import Silmaril.Wasm.Validation.Check.Validate

@[expose] public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Validation

/-- The context and ordered signatures used at the ordinary module checker's body checks. -/
structure BodyInputs where
  context : Context
  signatures : List DefType
  imports : List CExternType

/-- Run the ordinary module checker's context-building steps. -/
def bodyInputs? (m : Module) : Option BodyInputs := do
  let K := defaultCheckers
  let types ← K.types? {} m.types
  let imports ← m.imports.mapM (K.import? { types })
  let signatures ← m.funcs.mapM (fun f => ({ types } : Context).type? f.type)
  let base := moduleCtx' m types imports signatures
  let tags ← m.tags.mapM (K.tag? base)
  let globals ← K.globals? base m.globals
  let tables ← m.tables.mapM (K.table? base)
  let elems := m.elems.map fun e => base.closeRef e.type
  return ⟨moduleCtx m base imports tags globals tables elems, signatures, imports⟩

/-- The remaining checks use those inputs, with the original function list and signature order. -/
def finishValidation (m : Module) (inputs : BodyInputs) : Option CModuleType := do
  let K := defaultCheckers
  let C := inputs.context
  let elems := C.elems
  if m.memories.all K.mem && allPairs (K.func C) m.funcs inputs.signatures &&
      m.data.all (K.data C) && allPairs (fun e rt => K.elem? C e == some rt) m.elems elems &&
      m.start.all (K.start C) then
    let exports ← m.exports.mapM (K.export? C)
    if (m.exports.map Export.name).Nodup then some ⟨inputs.imports, exports⟩ else none
  else none

/-- The context extraction used by this fixture agrees with the ordinary validator. -/
theorem validate_eq_bodyInputs (m : Module) :
    validate? m = (bodyInputs? m).bind (finishValidation m) := by
  simp only [validate?, checkModule?, bodyInputs?, finishValidation, Option.bind_eq_bind,
    Option.bind_assoc, Option.pure_def, Option.bind_some]
  rfl

/-- A body at a defined-function ordinal meets `FuncOk` in the complete module context. -/
def BodyValidAt (m : Module) (ordinal : Nat) : Prop :=
  ∃ inputs f signature, bodyInputs? m = some inputs ∧
    m.funcs[ordinal]? = some f ∧ inputs.signatures[ordinal]? = some signature ∧
    FuncOk inputs.context f signature

end SqliteWasm
