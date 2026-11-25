module

public import SqliteWasm.ReactorValidation
import SqliteWasmArtifactEntries

namespace SqliteWasm.GuardEvidence

open SqliteWasmArtifact Silmaril.Wasm Silmaril.Wasm.Validation

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private def element : Elem :=
  sqlite.elems.headD ⟨⟨false, .abstract .func⟩, [], .declarative⟩

private def initChecks (input : BodyInputs) (start width : Nat) : Bool :=
  ((element.init.drop start).take width).all fun ex =>
    constC input.context ex (.refv (input.context.closeRef element.type))

private def initRange? (start width : Nat) : Option Bool :=
  (bodyInputs? sqlite).map fun input => initChecks input start width

sqlite_check_eq elements : sqlite.elems = [element]
sqlite_check_eq initCount : element.init.length = 342
sqlite_check_eq elementType : (bodyInputs? sqlite).map
    (fun p => tyOkC p.context.toTypeCtx (p.context.closeRef element.type)) = some true
sqlite_check_eq elementMode : (bodyInputs? sqlite).map
    (fun p => elemModeCheck constC p.context element.mode (p.context.closeRef element.type)) = some true
sqlite_check_eq init000 : initRange? 0 32 = some true
sqlite_check_eq init032 : initRange? 32 32 = some true
sqlite_check_eq init064 : initRange? 64 32 = some true
sqlite_check_eq init096 : initRange? 96 32 = some true
sqlite_check_eq init128 : initRange? 128 32 = some true
sqlite_check_eq init160 : initRange? 160 32 = some true
sqlite_check_eq init192 : initRange? 192 32 = some true
sqlite_check_eq init224 : initRange? 224 32 = some true
sqlite_check_eq init256 : initRange? 256 32 = some true
sqlite_check_eq init288 : initRange? 288 32 = some true
sqlite_check_eq init320 : initRange? 320 22 = some true

/-- Consecutive initializer checks through the end of the quoted list. -/
private def Ranges {α : Type} (p : α → Bool) (xs : List α) : Nat → List Nat → Prop
  | start, [] => xs.length ≤ start
  | start, width :: widths =>
    ((xs.drop start).take width).all p = true ∧ Ranges p xs (start + width) widths

private theorem checkRanges {α : Type} {p : α → Bool} {xs : List α}
    {start : Nat} {widths : List Nat} (checked : Ranges p xs start widths) :
    (xs.drop start).all p = true := by
  induction widths generalizing start with
  | nil => rw [List.drop_eq_nil_of_le (show xs.length ≤ start from checked)]; rfl
  | cons width widths ih =>
    obtain ⟨head, tail⟩ := checked
    have rest := ih tail
    rw [← List.take_append_drop width (xs.drop start), List.all_append, head, List.drop_drop, rest]
    rfl

private theorem fromRange {inputs : BodyInputs} {start width : Nat}
    (prepared : bodyInputs? sqlite = some inputs)
    (checked : initRange? start width = some true) : initChecks inputs start width = true := by
  simpa only [initRange?, prepared, Option.map_some, Option.some.injEq] using checked

private theorem allInitializers {inputs : BodyInputs} (prepared : bodyInputs? sqlite = some inputs) :
    element.init.all (fun ex => constC inputs.context ex (.refv (inputs.context.closeRef element.type))) = true := by
  have ranges : Ranges
      (fun ex => constC inputs.context ex (.refv (inputs.context.closeRef element.type)))
      element.init 0 [32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 22] :=
    ⟨fromRange prepared init000,
    fromRange prepared init032,
    fromRange prepared init064,
    fromRange prepared init096,
    fromRange prepared init128,
    fromRange prepared init160,
    fromRange prepared init192,
    fromRange prepared init224,
    fromRange prepared init256,
    fromRange prepared init288,
    fromRange prepared init320, by change element.init.length ≤ 342; exact initCount.le⟩
  simpa only [List.drop_zero] using checkRanges ranges

/-- The prepared context closes the same element types used by the section checker. -/
private theorem inputElems {m : Module} {p : BodyInputs} (h : bodyInputs? m = some p) :
    p.context.elems = m.elems.map (fun e => p.context.closeRef e.type) := by
  simp only [bodyInputs?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
  rfl

private theorem reactorElementGuard {inputs : BodyInputs} (prepared : bodyInputs? sqlite = some inputs) :
    allPairs (fun e rt => defaultCheckers.elem? inputs.context e == some rt)
      sqlite.elems inputs.context.elems = true := by
  have hty : tyOkC inputs.context.toTypeCtx (inputs.context.closeRef element.type) = true := by
    simpa only [prepared, Option.map_some, Option.some.injEq] using elementType
  have hmode : elemModeCheck constC inputs.context element.mode (inputs.context.closeRef element.type) = true := by
    simpa only [prepared, Option.map_some, Option.some.injEq] using elementMode
  have done : defaultCheckers.elem? inputs.context element = some (inputs.context.closeRef element.type) := by
    change elemCheck? tyOkC constC inputs.context element = _
    simp only [elemCheck?, hty, allInitializers prepared, hmode, Bool.and_self, ite_true]
  rw [inputElems prepared, elements, List.map_cons, List.map_nil]
  simp only [allPairs, done, beq_self_eq_true, Bool.and_self]

sqlite_check_eq memoryGuard : sqlite.memories.all defaultCheckers.mem = true
sqlite_check_eq dataGuard : (bodyInputs? sqlite).map
    (fun inputs => sqlite.data.all (defaultCheckers.data inputs.context)) = some true
sqlite_check_eq startGuard : (bodyInputs? sqlite).map
    (fun inputs => sqlite.start.all (defaultCheckers.start inputs.context)) = some true
sqlite_check_eq exportGuard : ((bodyInputs? sqlite).bind
    (fun inputs => sqlite.exports.mapM (defaultCheckers.export? inputs.context))).isSome = true
sqlite_check_eq namesGuard : decide (sqlite.exports.map Export.name).Nodup = true

/-- The full ordinary validator succeeds if all prepared body checks pass. -/
public theorem finalize
    (bodies : (bodyInputs? sqlite).any (fun inputs =>
      allPairs (defaultCheckers.func inputs.context) sqlite.funcs inputs.signatures) = true) :
    (validate? sqlite).isSome = true := by
  cases prepared : bodyInputs? sqlite with
  | none => simp [prepared] at bodies
  | some inputs =>
    have validatedBodies : allPairs (defaultCheckers.func inputs.context)
        sqlite.funcs inputs.signatures = true := by
      simpa only [prepared, Option.any_some] using bodies
    have data : sqlite.data.all (defaultCheckers.data inputs.context) = true := by
      simpa only [prepared, Option.map_some, Option.some.injEq] using dataGuard
    have start : sqlite.start.all (defaultCheckers.start inputs.context) = true := by
      simpa only [prepared, Option.map_some, Option.some.injEq] using startGuard
    have exportsOk : (sqlite.exports.mapM (defaultCheckers.export? inputs.context)).isSome := by
      simpa only [prepared, Option.bind_some] using exportGuard
    obtain ⟨xtE, hexports⟩ := Option.isSome_iff_exists.mp exportsOk
    rw [validate_eq_bodyInputs, prepared]
    simp only [Option.bind_some, finishValidation, memoryGuard, validatedBodies, data,
      reactorElementGuard prepared, start, Bool.and_self, ↓reduceIte, hexports,
      Option.bind_eq_bind, of_decide_eq_true namesGuard, Option.isSome_some]

end SqliteWasm.GuardEvidence
