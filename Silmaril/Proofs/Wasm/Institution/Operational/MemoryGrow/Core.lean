module

public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Thms
public import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryGrow.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryGrow.Proofs

open Execution Execution.Core Numerics
open Silmaril.Wasm.SingleThreaded.Det

theorem core_sound {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame} {a : Nat}
    {m : Runtime.MemInst} (guard : Admitted m)
    (lookup : s.mem? f MemoryQuery.index = some (a, m.toCore))
    {q b : State} (e : Edge m q b) :
    Step Profile.spec host (coreConfig s f a m q) (coreConfig s f a m b) := by
  cases invert e with
  | grow d bytes grew =>
    have exactGrow := grow_toCore guard d.toNat
    rw [grew] at exactGrow
    exact .memory (.growSucceed (a := .i32) lookup exactGrow trivial)
  | fail d => exact .memory (.growFail (a := .i32) (n := d) lookup (.inl trivial))

private theorem memory_readback {H : Type} {s : Store H} {f : Frame} {a : Nat}
    {m : Runtime.MemInst} (guard : Admitted m)
    (lookup : s.mem? f MemoryQuery.index = some (a, m.toCore))
    {delta : BitVec 32} {input : List Admin} {b : Config H}
    (step : MemoryStep Profile.spec ⟨s, f, input⟩ b)
    (support : List.Sublist input (coreConfig s f a m (.request delta)).code) :
    ∃ out, input = (coreConfig s f a m (.request delta)).code ∧
      Edge m (.request delta) out ∧ b = coreConfig s f a m out := by
  cases step with
  | @growSucceed _ _ x w n address old next found grew _ =>
    have opcode := support.subset (List.Mem.tail _ (List.Mem.head _))
    simp [coreConfig] at opcode
    subst x
    have code := support.eq_of_length rfl
    simp only [coreConfig, List.cons.injEq, Admin.plain.injEq, and_true] at code
    cases w
    case i64 => cases (Instr.intConst.inj code).1
    have same : n = delta := eq_of_heq (Instr.intConst.inj code).2
    subst n
    rw [lookup] at found
    obtain ⟨rfl, rfl⟩ := Option.some.inj found
    change m.toCore.grow? delta.toNat = some next at grew
    rw [grow_toCore guard] at grew
    cases h : Memory.grow? m.data m.max delta.toNat with
    | none => simp [h] at grew
    | some bytes =>
      simp only [h, Option.map_some, Option.some.injEq] at grew
      subst next
      exact ⟨.grown bytes, rfl, fact (.grow delta bytes h), rfl⟩
  | @growFail _ _ x w n address old found _ =>
    have opcode := support.subset (List.Mem.tail _ (List.Mem.head _))
    simp [coreConfig] at opcode
    subst x
    have code := support.eq_of_length rfl
    simp only [coreConfig, List.cons.injEq, Admin.plain.injEq, and_true] at code
    cases w
    case i64 => cases (Instr.intConst.inj code).1
    have same : n = delta := eq_of_heq (Instr.intConst.inj code).2
    subst n
    exact ⟨.failed, rfl, fact (.fail delta), rfl⟩
  | _ =>
    have check := support.subset
    simp [coreConfig] at check

private theorem nonmemory_impossible {k : Fam} {args : List Val} (diff : k ≠ .memory)
    (shape : FamShape k (vals args ++ [.plain (.memoryGrow MemoryQuery.index)])) : False := by
  obtain ⟨_, op, code, _, kind⟩ := shape
  have last := congrArg List.getLast? code
  simp [List.getLast?_append] at last
  subst op
  exact diff kind.symm

theorem core_readback {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame} {a : Nat}
    {m : Runtime.MemInst} (guard : Admitted m)
    (lookup : s.mem? f MemoryQuery.index = some (a, m.toCore))
    {q : State} {b : Config H} (step : Step Profile.spec host (coreConfig s f a m q) b) :
    ∃ out, Edge m q out ∧ b = coreConfig s f a m out := by
  cases q with
  | grown bytes =>
    exact (Step.not_vals (vs := [.i32 (BitVec.ofNat 32 (Memory.size m.data))]) step).elim
  | failed => exact (Step.not_vals (vs := [.i32 (-1)]) step).elim
  | request delta =>
    let op := Admin.plain (.memoryGrow MemoryQuery.index)
    change Step Profile.spec host ⟨s, f, vals [.i32 delta] ++ [op]⟩ b at step
    obtain ⟨saved, args, middle, split, head, rfl⟩ := Step.noncontrol_vals_inv (by decide) step
    have support : List.Sublist (vals args ++ [op]) (coreConfig s f a m (.request delta)).code := by
      change List.Sublist _ (vals [.i32 delta] ++ [op])
      rw [split, vals_append, List.append_assoc]
      exact List.sublist_append_right _ _
    cases head with
    | memory h =>
      obtain ⟨out, whole, edge, rfl⟩ := memory_readback guard lookup h support
      have length := congrArg List.length whole
      change (vals args ++ [op]).length = 2 at length
      have total := congrArg List.length split
      simp only [vals, List.length_append, List.length_map, List.length_cons, List.length_nil] at length total
      have hs : saved = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst saved
      cases out <;> exact ⟨_, edge, rfl⟩
    | parametric h => exact (nonmemory_impossible (by decide) (ParametricStep.shape h)).elim
    | numeric h => exact (nonmemory_impossible (by decide) (NumericStep.shape h)).elim
    | vector h => exact (nonmemory_impossible (by decide) (VectorStep.shape h)).elim
    | «variable» h => exact (nonmemory_impossible (by decide) (VariableStep.shape h)).elim
    | table h => exact (nonmemory_impossible (by decide) (TableStep.shape h)).elim
    | reference h => exact (nonmemory_impossible (by decide) (RefStep.shape h)).elim
    | aggregate h => exact (nonmemory_impossible (by decide) (AggregateStep.shape h)).elim

end Silmaril.Wasm.Institution.Operational.MemoryGrow.Proofs
