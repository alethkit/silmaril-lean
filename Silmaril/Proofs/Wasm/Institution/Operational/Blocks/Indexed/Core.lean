module

public import Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Native.Defs
public import Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Wasm.Institution.Operational.Blocks.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Context.Thms
import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.V1.ToCore.DefTypes

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Proofs.Core

open Execution.Core
open Execution.Runtime (Value)
open SingleThreaded.Det (noHost)

theorem type_idx (m : Execution.Runtime.ModuleInst) (i : TypeIdx) :
    m.toCore.blockType? (.typeIdx i) =
      m.types[i.toNat]?.map (fun ft => (ft.params.map Validation.Ty.num, ft.results.map Validation.Ty.num)) := by
  change ((m.types.map Wasm.V1.FuncType.toDefType)[i.toNat]?.bind Validation.DefType.funcType?) = _
  rw [List.getElem?_map]
  cases m.types[i.toNat]? <;> simp [Validation.DefType.funcType?, Wasm.V1.FuncType.toDefType_expand]

private theorem encode_values (xs : List Value) :
    Locals.coreCodec.encode (Locals.values xs) = Blocks.Context.coreValues xs := by
  unfold Locals.Codec.encode Locals.values
  rw [List.map_map]
  change _ = vals (xs.map Value.toCore)
  simp only [Locals.coreCodec, Locals.coreInstr, vals, List.map_map]
  apply List.map_congr_left
  intro v _
  rcases v with ⟨t, bits⟩
  cases t <;> rfl

private theorem source_iff {H : Type} {P : Numerics.Profile} {s : Store H} {site : Site}
    {locals args : List Value} {body : Body} {dst : Config H} (resolved : site.Resolved)
    (arity : args.length = site.signature.params.length) :
    Step P noHost (coreConfig s site (.source locals args body)) dst ↔
      dst = coreConfig s site (body.entered locals args) := by
  have lookup : (site.declaration.module.toCore).blockType? (.typeIdx site.index) =
      some (site.signature.params.map Validation.Ty.num, site.signature.results.map Validation.Ty.num) := by
    rw [type_idx, resolved]
    rfl
  let code := body.instructions Locals.coreInstr (.br ⟨0⟩) .return_
  have before : coreConfig s site (.source locals args body) =
      ⟨s, (⟨locals, site.declaration.module⟩ : Execution.Runtime.Frame).toCore, vals ((site.saved ++ args).map Value.toCore) ++ [.plain (.block (.typeIdx site.index) code)]⟩ := by
    simp [coreConfig, State.frame, State.code, coreSyntax, code, vals_append, List.append_assoc]
  have after : coreConfig s site (body.entered locals args) =
      ⟨s, (⟨locals, site.declaration.module⟩ : Execution.Runtime.Frame).toCore, Blocks.Context.coreValues site.saved ++
        [.label site.signature.results.length [] (Blocks.Context.coreValues args ++ expression code)]⟩ := by
    cases body with
    | locals bodyCode =>
      have encoded : Locals.coreCodec.encode bodyCode = expression code := by
        change bodyCode.map (Admin.plain ∘ Locals.coreInstr) =
          (bodyCode.map Locals.coreInstr).map Admin.plain
        exact (List.map_map ..).symm
      simp only [coreConfig, State.frame, State.code, coreSyntax, Body.entered,
        Locals.Codec.encode_append, encode_values, encoded]
    | branch | return_ => rfl
  rw [before, after, Blocks.core_block_step_iff]
  constructor
  · rintro ⟨saved, used, params, results, split, found, size, rfl⟩
    change site.declaration.module.toCore.blockType? (.typeIdx site.index) = _ at found
    rw [lookup] at found
    cases found
    rw [List.map_append] at split
    have length : args.length = used.length := arity.trans (by simpa using size.symm)
    obtain ⟨rfl, rfl⟩ := List.append_inj' split (show (args.map Value.toCore).length = used.length by simpa using length)
    simp [Blocks.Context.coreValues]
  · intro eq
    exact ⟨site.saved.map Value.toCore, (args.map Value.toCore), _, _, List.map_append, lookup, by simpa using arity,
      by simpa [Blocks.Context.coreValues] using eq⟩

theorem step_iff {H : Type} {P : Numerics.Profile} {s : Store H} {site : Site} {a : State}
    {dst : Config H} (ready : Admitted site a) :
    Step P noHost (coreConfig s site a) dst ↔
      ∃ out, Edge site a out ∧ dst = coreConfig s site out := by
  cases a with
  | source locals args body =>
    have arity : args.length = site.signature.params.length := by
      simpa using congrArg List.length ready.2.2.1
    rw [source_iff ready.1 arity]
    constructor
    · intro eq
      exact ⟨_, .enter locals args body, eq⟩
    · rintro ⟨_, edge, eq⟩
      cases edge
      exact eq
  | label a =>
    change Step P noHost
      ⟨s, (⟨a.locals, site.declaration.module⟩ : Execution.Runtime.Frame).toCore, Blocks.Context.coreValues site.saved ++
        .label site.signature.results.length [] (Locals.coreCodec.encode a.code) :: []⟩ dst ↔ _
    rw [Blocks.Context.core_label_iff]
    simp only [List.append_nil]
    constructor
    · rintro (⟨mid, inside, rfl⟩ | ⟨code, pop, rfl⟩)
      · obtain ⟨next, edge, rfl⟩ := Locals.core_step_iff.mp inside
        exact ⟨.label next, .reduce edge, rfl⟩
      · obtain ⟨results, code, rfl⟩ := Blocks.core_locals_label_exit pop
        have same : a = ⟨a.locals, Locals.values results⟩ := by cases a; simp_all
        exact ⟨.done a.locals results, same.symm ▸ .fallthrough _ _, rfl⟩
    · rintro ⟨out, edge, rfl⟩
      cases edge with
      | reduce move => exact .inl ⟨_, Locals.core_sound move, rfl⟩
      | fallthrough locals results =>
        refine .inr ⟨_, ?_, rfl⟩
        rw [encode_values]
        exact LabelExit.vals (n := site.signature.results.length) (cont := []) (results.map Value.toCore)
  | branch locals stack =>
    change Step P noHost ⟨s, (⟨locals, site.declaration.module⟩ : Execution.Runtime.Frame).toCore, Blocks.Context.coreValues site.saved ++
      .label site.signature.results.length [] (Blocks.Context.coreValues stack ++ [.plain (.br ⟨0⟩)]) :: []⟩ dst ↔ _
    rw [Blocks.Context.core_label_iff]
    simp only [List.append_nil]
    constructor
    · rintro (⟨mid, inside, _⟩ | ⟨code, pop, rfl⟩)
      · exact (inside.br_vals_stuck).elim
      · obtain ⟨scratch, payload, split, size, rfl⟩ := BranchExit.core_label_br_zero pop
        obtain ⟨scratch, payload, stackEq, rfl, rfl⟩ := List.map_eq_append_iff.mp split
        refine ⟨.done locals payload, ?_, by simp [coreConfig, State.code, State.frame, coreSyntax]⟩
        rw [stackEq]
        exact .branch locals scratch payload (by simpa using size)
    · rintro ⟨out, edge, rfl⟩
      cases edge with
      | branch locals scratch results arity =>
        refine .inr ⟨_, ?_, rfl⟩
        simpa only [coreSyntax, Blocks.Context.coreValues, List.map_append, vals_append, List.append_assoc,
          List.singleton_append, expression, List.map_nil, List.append_nil] using
          LabelExit.brZero (l := ⟨0⟩) (cont := []) (vs' := scratch.map Value.toCore)
            (vs := results.map Value.toCore) (rest := []) rfl (by simpa using arity)
  | return_ locals stack =>
    change Step P noHost ⟨s, (⟨locals, site.declaration.module⟩ : Execution.Runtime.Frame).toCore, Blocks.Context.coreValues site.saved ++
      .label site.signature.results.length [] (Blocks.Context.coreValues stack ++ [.plain .return_]) :: []⟩ dst ↔ _
    rw [Blocks.Context.core_label_iff]
    simp only [List.append_nil]
    constructor
    · rintro (⟨mid, inside, _⟩ | ⟨code, pop, rfl⟩)
      · exact (CallFrame.core_return_stuck inside).elim
      · rw [CallFrame.core_return_label_result (tail := []) pop]
        exact ⟨_, .return_ locals stack, rfl⟩
    · rintro ⟨out, edge, rfl⟩
      cases edge with
      | return_ =>
        refine .inr ⟨_, ?_, rfl⟩
        simpa only [List.append_nil, coreSyntax, Blocks.Context.coreValues] using
          (LabelExit.ret (vs := stack.map Value.toCore) (rest := []) (cont := []) (n := site.signature.results.length))
  | done locals results =>
    constructor
    · intro move
      have inside : Step P noHost ⟨s, (⟨locals, site.declaration.module⟩ : Execution.Runtime.Frame).toCore, Blocks.Context.coreValues (site.saved ++ results)⟩ dst := by
        simpa [coreConfig, State.code, State.frame, coreSyntax, Blocks.Context.coreValues, vals_append, List.map_append] using move
      exact (Step.not_vals inside).elim
    · rintro ⟨_, edge, _⟩
      cases edge
  | pendingReturn locals stack =>
    constructor
    · intro move
      have inside : Step P noHost ⟨s, (⟨locals, site.declaration.module⟩ : Execution.Runtime.Frame).toCore,
          Blocks.Context.coreValues (site.saved ++ stack) ++ [.plain .return_]⟩ dst := by
        simpa [coreConfig, State.code, State.frame, coreSyntax, Blocks.Context.coreValues, vals_append, List.map_append, List.append_assoc] using move
      exact (CallFrame.core_return_stuck (tail := []) inside).elim
    · rintro ⟨_, edge, _⟩
      cases edge

end Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Proofs.Core
