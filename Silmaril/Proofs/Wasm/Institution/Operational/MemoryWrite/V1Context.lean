module

public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryWrite.V1
import Silmaril.Wasm.V1.Execution.Inversion

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryWrite.Proofs.V1Context

open Execution.Runtime (Frame MemAddr MemInst Value)
open Wasm.V1.Execution

private inductive MemoryHead : Admin → Nat → Prop where
  | load (arg : Wasm.V1.MemArg) : MemoryHead (.source (.intLoad .i32 none arg)) 1
  | store (arg : Wasm.V1.MemArg) : MemoryHead (.source (.intStore .i32 none arg)) 2

private theorem MemoryHead.nonvalue {op : Admin} {arity : Nat} (h : MemoryHead op arity) :
    asValue? op = none := by
  cases h <;> rfl

private theorem at_head {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {stack used : List Value} {op : Admin} {tail : List Admin} {arity : Nat} {dst : Config H}
    (shape : MemoryHead op arity) (len : used.length = arity)
    (code : values used ++ op :: [] = values stack ++ op :: tail)
    (step : Step host ⟨s, f, values used ++ [op]⟩ dst) :
    ∃ kept used' mid, stack = kept ++ used' ∧ used'.length = arity ∧
      Step host ⟨s, f, values used' ++ [op]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, values kept ++ mid.code ++ tail⟩ := by
  obtain ⟨rfl, _, rfl⟩ := values_cons_inj shape.nonvalue shape.nonvalue code
  exact ⟨[], used, dst, rfl, len, step, by cases dst; simp [values]⟩

set_option linter.unusedSimpArgs false in
private theorem cut {H : Type} {host : HostSemantics H} {src dst : Config H}
    {op : Admin} {arity : Nat} (shape : MemoryHead op arity) (move : Step host src dst)
    {stack : List Value} {tail : List Admin} (code : src.code = values stack ++ op :: tail) :
    ∃ kept used mid, stack = kept ++ used ∧ used.length = arity ∧
      Step host ⟨src.store, src.frame, values used ++ [op]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, values kept ++ mid.code ++ tail⟩ := by
  have first : firstRedex src.code = some op := by
    rw [code]
    simp [firstRedex_cons, shape.nonvalue]
  induction move generalizing stack tail with
  | @context s s' f f' before after step saved rest ih =>
    have live := step.firstRedex_ne_none
    cases scan : firstRedex before with
    | none => exact (live scan).elim
    | some actual =>
      have same : actual = op := by simpa [scan] using first
      subst actual
      obtain ⟨more, suffix, middle⟩ := firstRedex_eq_some scan
      have combined : values (saved ++ more) ++ op :: (suffix ++ rest) = values stack ++ op :: tail := by
        simpa [middle, List.append_assoc] using code
      obtain ⟨rfl, _, rfl⟩ := values_cons_inj shape.nonvalue shape.nonvalue combined
      obtain ⟨kept, used, mid, rfl, len, leaf, eq⟩ := ih middle scan
      refine ⟨saved ++ kept, used, mid, (List.append_assoc ..).symm, len, leaf, ?_⟩
      change (⟨s', f', after⟩ : Config H) = _ at eq
      simpa only [values_append, List.append_assoc] using congrArg
        (fun cfg : Config H => (⟨cfg.store, cfg.frame, values saved ++ cfg.code ++ rest⟩ : Config H)) eq
  | intLoad s f t packed arg address a m v found read =>
    cases shape <;>
      simp only [firstRedex_value_cons] at first <;> simp [firstRedex_cons, asValue?] at first
    obtain ⟨rfl, rfl, rfl⟩ := first
    exact at_head (.load _) (used := [Value.int .i32 address]) rfl code
      (.intLoad s f _ _ _ _ a m v found read)
  | intLoadTrap s f t packed arg address a m found read =>
    cases shape <;>
      simp only [firstRedex_value_cons] at first <;> simp [firstRedex_cons, asValue?] at first
    obtain ⟨rfl, rfl, rfl⟩ := first
    exact at_head (.load _) (used := [Value.int .i32 address]) rfl code
      (.intLoadTrap s f _ _ _ _ a m found read)
  | intStore s f t packed arg address word a m out found write =>
    cases shape <;>
      simp only [firstRedex_value_cons] at first <;> simp [firstRedex_cons, asValue?] at first
    obtain ⟨rfl, rfl, rfl⟩ := first
    exact at_head (.store _) (used := [Value.int .i32 address, Value.int .i32 word]) rfl code
      (.intStore s f _ _ _ _ _ a m out found write)
  | intStoreTrap s f t packed arg address word a m found write =>
    cases shape <;>
      simp only [firstRedex_value_cons] at first <;> simp [firstRedex_cons, asValue?] at first
    obtain ⟨rfl, rfl, rfl⟩ := first
    exact at_head (.store _) (used := [Value.int .i32 address, Value.int .i32 word]) rfl code
      (.intStoreTrap s f _ _ _ _ _ a m found write)
  | pure s f step =>
    cases step <;> cases shape <;>
      simp only [List.append_assoc, firstRedex_append, firstRedex_values, Option.none_or,
        values_cons, values_nil, List.nil_append, List.cons_append, firstRedex_value_cons] at first <;>
      simp [firstRedex_cons, asValue?] at first
  | _ =>
    cases shape <;>
      simp only [List.append_assoc, firstRedex_append, firstRedex_values, Option.none_or,
        values_cons, values_nil, List.nil_append, List.cons_append, firstRedex_value_cons] at first <;>
      simp [firstRedex_cons, asValue?] at first

theorem load_step_iff {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg} {address : BitVec 32}
    {saved : List Value} {tail : List Admin} {dst : Config H}
    (lookup : frameMemory s f = some (a, m)) :
    Step host ⟨s, f, values saved ++ MemoryQuery.v1CodeAt immediate (.load address) ++ tail⟩ dst ↔
      ∃ out, MemoryQuery.EdgeAt m.data immediate.offset.val (.load address) out ∧
        dst = ⟨s, f, values saved ++ MemoryQuery.v1CodeAt immediate out ++ tail⟩ := by
  constructor
  · intro move
    have code : (values saved ++ MemoryQuery.v1CodeAt immediate (.load address) ++ tail) =
        values (saved ++ [Value.int .i32 address]) ++ .source (.intLoad .i32 none immediate) :: tail := by
      simp [values, MemoryQuery.v1CodeAt, value, Value.int]
    obtain ⟨kept, used, mid, split, len, head, rfl⟩ := cut (.load immediate) move code
    obtain ⟨rfl, rfl⟩ := List.append_inj' split len.symm
    obtain ⟨out, edge, rfl⟩ := MemoryQuery.v1_readback_at immediate lookup (query := .load address) head
    exact ⟨out, edge, rfl⟩
  · rintro ⟨out, edge, rfl⟩
    exact .context (MemoryQuery.v1_sound_at immediate lookup edge) saved tail

theorem store_step_iff {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg} {address word : BitVec 32}
    {saved : List Value} {tail : List Admin} {dst : Config H}
    (lookup : frameMemory s f = some (a, m)) :
    Step host ⟨s, f, values saved ++ (v1ConfigAt immediate s f a m (.store address word)).code ++ tail⟩ dst ↔
      ∃ out, EdgeAt m.data immediate.offset.val (.store address word) out ∧
        let next := v1ConfigAt immediate s f a m out
        dst = ⟨next.store, next.frame, values saved ++ next.code ++ tail⟩ := by
  constructor
  · intro move
    have code : (values saved ++ (v1ConfigAt immediate s f a m (.store address word)).code ++ tail) =
        values (saved ++ [Value.int .i32 address, Value.int .i32 word]) ++
          .source (.intStore .i32 none immediate) :: tail := by simp [values, v1ConfigAt, value, Value.int]
    obtain ⟨kept, used, mid, split, len, head, rfl⟩ := cut (.store immediate) move code
    obtain ⟨rfl, rfl⟩ := List.append_inj' split len.symm
    obtain ⟨out, edge, rfl⟩ := V1.readback immediate lookup (q := .store address word) head
    exact ⟨out, edge, rfl⟩
  · rintro ⟨out, edge, rfl⟩
    exact .context (V1.sound immediate lookup edge) saved tail

set_option linter.unusedSimpArgs false in
private theorem label_stays {body out : List Admin} {op : Admin} {operands n : Nat}
    (shape : MemoryHead op operands) (first : firstRedex body = some op)
    (pop : PureStep [.label n [] body] out) : False := by
  generalize eq : ([.label n [] body] : List Admin) = source at pop
  have head : firstRedex source = some (.label n [] body) := by rw [← eq]; rfl
  cases pop <;>
    (try simp only [List.append_assoc, firstRedex_append, firstRedex_values, Option.none_or,
      values_cons, values_nil, List.nil_append, List.cons_append, firstRedex_value_cons] at head) <;>
    simp [firstRedex_cons, asValue?] at head
  all_goals
    obtain ⟨_, _, rfl⟩ := head
    cases shape <;> simp [List.append_assoc, firstRedex_cons, asValue?] at first

set_option linter.unusedSimpArgs false in
private theorem frame_stays {body out : List Admin} {f : Frame} {n : Nat}
    (pop : PureStep [.frame n f [.label n [] body]] out) : False := by
  generalize eq : ([.frame n f [.label n [] body]] : List Admin) = source at pop
  have head : firstRedex source = some (.frame n f [.label n [] body]) := by rw [← eq]; rfl
  cases pop <;>
    (try simp only [List.append_assoc, firstRedex_append, firstRedex_values, Option.none_or,
      values_cons, values_nil, List.nil_append, List.cons_append, firstRedex_value_cons] at head) <;>
    simp [firstRedex_cons, asValue?] at head
  all_goals
    have first := congrArg firstRedex head.2.2
    simp [List.append_assoc, firstRedex_cons, asValue?] at first

private theorem activation_iff {H : Type} {host : HostSemantics H} {s : Store H}
    {caller callee : Frame} {result : Option NumType} {saved : List Value} {tail body : List Admin}
    {op : Admin} {operands : Nat} {dst : Config H}
    (shape : MemoryHead op operands) (first : firstRedex body = some op) :
    Step host ⟨s, caller, v1ActivationCode result callee saved tail body⟩ dst ↔
      ∃ mid, Step host ⟨s, callee, body⟩ mid ∧
        dst = ⟨mid.store, caller, v1ActivationCode result mid.frame saved tail mid.code⟩ := by
  let n := result.toList.length
  constructor
  · intro move
    obtain ⟨outer, inner | ⟨_, pop, _, _⟩⟩ :=
      move.frame_inv (p := saved) (q := tail) (n := n) (fr := callee) (body := [.label n [] body]) rfl
    · obtain ⟨active, code, step, rendered⟩ := inner
      rcases step.label_inv (p := []) (q := []) (n := n) (cont := []) (body := body) rfl with
        ⟨next, move, equation⟩ | ⟨_, pop, _, _, _⟩
      · refine ⟨⟨dst.store, active, next⟩, move, ?_⟩
        have finalCode : dst.code = v1ActivationCode result active saved tail next := by
          simp only [values_nil, List.nil_append] at equation
          rw [rendered, equation]
          rfl
        cases dst
        simp_all
      · exact (label_stays shape first pop).elim
    · exact (frame_stays pop).elim
  · rintro ⟨mid, move, rfl⟩
    simpa only [v1ActivationCode, List.append_assoc, List.singleton_append] using
      Step.context (Step.frame (Step.label move n []) n caller) saved tail

theorem load_activation_iff {H : Type} {host : HostSemantics H} {s : Store H}
    {caller callee : Frame} {result : Option NumType} {callerSaved saved : List Value}
    {callerTail tail : List Admin} {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg}
    {address : BitVec 32} {dst : Config H} (lookup : frameMemory s callee = some (a, m)) :
    Step host ⟨s, caller, v1ActivationCode result callee callerSaved callerTail
      (values saved ++ MemoryQuery.v1CodeAt immediate (.load address) ++ tail)⟩ dst ↔
      ∃ out, MemoryQuery.EdgeAt m.data immediate.offset.val (.load address) out ∧
        dst = ⟨s, caller, v1ActivationCode result callee callerSaved callerTail
          (values saved ++ MemoryQuery.v1CodeAt immediate out ++ tail)⟩ := by
  have first : firstRedex (values saved ++ MemoryQuery.v1CodeAt immediate (.load address) ++ tail) =
      some (.source (.intLoad .i32 none immediate)) := by
    simp [MemoryQuery.v1CodeAt, firstRedex_cons, asValue?]
  rw [activation_iff (.load immediate) first]
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨out, edge, rfl⟩ := (load_step_iff lookup).mp move
    exact ⟨out, edge, rfl⟩
  · rintro ⟨out, edge, rfl⟩
    exact ⟨_, (load_step_iff lookup).mpr ⟨out, edge, rfl⟩, rfl⟩

theorem store_activation_iff {H : Type} {host : HostSemantics H} {s : Store H}
    {caller callee : Frame} {result : Option NumType} {callerSaved saved : List Value}
    {callerTail tail : List Admin} {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg}
    {address word : BitVec 32} {dst : Config H} (lookup : frameMemory s callee = some (a, m)) :
    Step host ⟨s, caller, v1ActivationCode result callee callerSaved callerTail
      (values saved ++ (v1ConfigAt immediate s callee a m (.store address word)).code ++ tail)⟩ dst ↔
      ∃ out, EdgeAt m.data immediate.offset.val (.store address word) out ∧
        let next := v1ConfigAt immediate s callee a m out
        dst = ⟨next.store, caller, v1ActivationCode result next.frame callerSaved callerTail
          (values saved ++ next.code ++ tail)⟩ := by
  have first : firstRedex
      (values saved ++ (v1ConfigAt immediate s callee a m (.store address word)).code ++ tail) =
      some (.source (.intStore .i32 none immediate)) := by
    simp [v1ConfigAt, firstRedex_cons, asValue?]
  rw [activation_iff (.store immediate) first]
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨out, edge, rfl⟩ := (store_step_iff lookup).mp move
    exact ⟨out, edge, rfl⟩
  · rintro ⟨out, edge, rfl⟩
    exact ⟨_, (store_step_iff lookup).mpr ⟨out, edge, rfl⟩, rfl⟩

theorem frameMemory_setBytes {H : Type} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (lookup : frameMemory s f = some (a, m)) (bytes : ByteArray) :
    frameMemory (setMemory s a { m with data := bytes }) f = some (a, { m with data := bytes }) := by
  unfold frameMemory at lookup ⊢
  cases slot : f.module.memories[0]? with
  | none => simp [slot] at lookup
  | some addr =>
    cases allocated : s.memories[addr.value]? with
    | none => simp [slot, allocated] at lookup
    | some inst =>
      simp [slot, allocated] at lookup
      obtain ⟨rfl, rfl⟩ := lookup
      have h : addr.value < s.memories.length := (List.getElem?_eq_some_iff.mp allocated).1
      simp [setMemory, h]

end Silmaril.Wasm.Institution.Operational.MemoryWrite.Proofs.V1Context
