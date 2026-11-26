module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Body
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Proofs

open RVSDG (Port Tuple)
open SeaOfNodes.Diamond (Projection Slot)
open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Cfg Frame Terminator)
open Silmaril.MLIR.SCF.For (weakenVar)

variable {p : Profile} {args : List ValueSort} {Γ Δ : List Width} {w : Width}

private theorem get_appendVar (ref : Var Γ w) (arguments : Env Γ) (suffix : Env Δ) :
    (arguments.append suffix).get (appendVar Δ ref) = arguments.get ref := by
  induction ref with
  | here => cases arguments; rfl
  | there _ ih => cases arguments with | cons _ tail => exact ih tail

private theorem get_weakenVar (arguments : Env Δ) (input : Env Γ) (ref : Var Γ w) :
    (arguments.append input).get (weakenVar ref Δ) = input.get ref := by
  induction arguments with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem encodeHeap_get {cells : Nat} (heap : Heap cells) (index : Address cells) :
    (encodeHeap heap).get (cellVar index) = heap index := by
  induction cells with
  | zero => exact index.elim0
  | succ cells ih =>
    exact Fin.cases rfl (fun i => ih (fun j => heap j.succ) i) index

private theorem eval_heapOperands {cells : Nat} (refs : HeapRefs cells Γ) (env : Env Γ)
    (heap : Heap cells) (ok : ∀ index, env.get (refs index) = heap index) :
    (heapOperands refs).eval env = encodeHeap heap := by
  induction cells with
  | zero => rfl
  | succ cells ih =>
    exact congrArg₂ (Env.cons (w := i64)) (ok 0)
      (ih (fun j => refs j.succ) (fun j => heap j.succ) (fun j => ok j.succ))

private theorem pack_operands (word : Var Γ i64) (refs : HeapRefs p.cells Γ) (env : Env Γ)
    (heap : Heap p.cells) (ok : HeapAgrees refs env heap) :
    (resultOperands (p := p) word refs).eval env = encodeResult p (env.get word) heap :=
  congrArg (Env.cons (env.get word)) (eval_heapOperands refs env heap ok)

private theorem arg_match (input : Tuple (Val p.cells) args) {sort : ValueSort} (port : Port args sort) :
    (encodeScalars p input).get (argVar port) = encodeValue p (input.get port) := by
  induction port with
  | head => cases input; rfl
  | tail _ ih => cases input with | cons _ rest => exact ih rest

private theorem entry_match (guard : Bool) (input : Tuple (Val p.cells) args) (heap : Heap p.cells) :
    Matches (entryRoute p args) (encodeEntry p guard input heap) input PUnit.unit := by
  intro sort wire
  cases wire with
  | arg port =>
    exact (get_weakenVar (encodeHeap heap) (encodeScalars p input) (argVar port)).trans
      (arg_match input port)
  | output index _ => exact index.elim0

private theorem entry_heap (guard : Bool) (input : Tuple (Val p.cells) args) (heap : Heap p.cells) :
    HeapAgrees (p := p) (entryHeap p args) (encodeEntry p guard input heap) heap :=
  fun index => (get_appendVar (cellVar index) (encodeHeap heap) (encodeScalars p input)).trans
    (encodeHeap_get heap index)

private theorem join_match (guard : Bool) (input : Tuple (Val p.cells) args)
    (initial final : Heap p.cells) (word : Word) :
    Matches (joinRoute p args) ((encodeResult p word final).append (encodeEntry p guard input initial))
      (.cons word input) PUnit.unit := by
  intro sort wire
  cases wire with
  | arg port =>
    cases port with
    | head => rfl
    | tail port =>
      exact (get_weakenVar (encodeResult p word final) (encodeEntry p guard input initial)
        (entryRoute p args (.arg port))).trans (entry_match guard input initial (.arg port))
  | output index _ => exact index.elim0

private theorem join_heap (guard : Bool) (input : Tuple (Val p.cells) args)
    (initial final : Heap p.cells) (word : Word) :
    HeapAgrees (p := p) (joinHeap p args)
      ((encodeResult p word final).append (encodeEntry p guard input initial)) final :=
  fun index => (get_appendVar (.there (cellVar index)) (encodeResult p word final)
    (encodeEntry p guard input initial)).trans (encodeHeap_get final index)

private def joinFrame (p : Profile) (word : Word) (heap : Heap p.cells) : Frame (Label p) :=
  ⟨.join, encodeResult p word heap⟩

private def armFrame (p : Profile) (slot : Slot) : Frame (Label p) := ⟨.arm slot, .nil⟩

private theorem arm_eval (graph : Graph args) (slot : Slot) (guard : Bool)
    (input : Tuple (Val p.cells) args) (initial : Heap p.cells) :
    (armBlock p graph slot).eval evalOp (fun term env => term.eval env) (encodeEntry p guard input initial) =
      let selected := (graph.arm (graph.merge.predecessor slot)).denote input initial
      Sum.inl (joinFrame p selected.1 selected.2) := by
  refine eval_lowerBody (graph.arm (graph.merge.predecessor slot))
    (fun word heap => Terminator.br ⟨Label.join, resultOperands (p := p) word heap⟩)
    (fun term env => term.eval env) (fun word heap => Sum.inl (joinFrame p word heap)) ?_
    (entryRoute p args) (entryHeap p args) _ input PUnit.unit initial
    (entry_match guard input initial) (entry_heap guard input initial)
  intro Δ word refs env heap ok
  exact congrArg (fun values => Sum.inl (Frame.mk (Label.join (p := p)) values))
    (pack_operands word refs env heap ok)

private theorem join_eval (graph : Graph args) (guard : Bool) (input : Tuple (Val p.cells) args)
    (initial : Heap p.cells) (word : Word) (heap : Heap p.cells) :
    (joinBlock p graph).eval evalOp (fun term env => term.eval env)
        ((encodeResult p word heap).append (encodeEntry p guard input initial)) =
      let result := graph.suffix.denote (.cons word input) heap
      Sum.inr (encodeResult p result.1 result.2) := by
  refine eval_lowerBody graph.suffix (fun word heap => Terminator.ret (resultOperands (p := p) word heap))
    (fun term env => term.eval env) (fun word heap => Sum.inr (encodeResult p word heap)) ?_
    (joinRoute p args) (joinHeap p args) _ (.cons word input) PUnit.unit heap
    (join_match guard input initial heap word) (join_heap guard input initial heap word)
  intro Δ result refs env final ok
  exact congrArg Sum.inr (pack_operands result refs env final ok)

private theorem entry_eval (graph : Graph args) (guard : Bool) (input : Tuple (Val p.cells) args)
    (initial : Heap p.cells) :
    (lower p graph).entry.eval evalOp (fun term env => term.eval env) (encodeEntry p guard input initial) =
      Sum.inl (armFrame p (graph.merge.slot (Projection.ofBool guard))) := by
  change Sum.inl (if (BitVec.ofBool guard).getLsbD 0 then armFrame p (graph.merge.slot .onTrue)
    else armFrame p (graph.merge.slot .onFalse)) = _
  rw [BitVec.getLsbD_ofBool]
  cases guard <;> rfl

private theorem run_entry (graph : Graph args) (guard : Bool) (input : Tuple (Val p.cells) args)
    (initial : Heap p.cells) (fuel : Nat) :
    (lower p graph).run evalOp (fuel + 1) (encodeEntry p guard input initial) =
      (lower p graph).runFrom evalOp fuel (encodeEntry p guard input initial)
        (armFrame p (graph.merge.slot (Projection.ofBool guard))) := by
  rw [Cfg.run, Cfg.runBlock, entry_eval]
  rfl

private theorem run_arm (graph : Graph args) (slot : Slot) (guard : Bool) (input : Tuple (Val p.cells) args)
    (initial : Heap p.cells) (fuel : Nat) :
    (lower p graph).runFrom evalOp (fuel + 1) (encodeEntry p guard input initial) (armFrame p slot) =
      let selected := (graph.arm (graph.merge.predecessor slot)).denote input initial
      (lower p graph).runFrom evalOp fuel (encodeEntry p guard input initial)
        (joinFrame p selected.1 selected.2) := by
  change (lower p graph).runBlock evalOp (encodeEntry p guard input initial) (fuel + 1)
    (armBlock p graph slot) (encodeEntry p guard input initial) = _
  rw [Cfg.runBlock, arm_eval]
  rfl

private theorem run_join (graph : Graph args) (guard : Bool) (input : Tuple (Val p.cells) args)
    (initial : Heap p.cells) (word : Word) (heap : Heap p.cells) (fuel : Nat) :
    (lower p graph).runFrom evalOp (fuel + 1) (encodeEntry p guard input initial) (joinFrame p word heap) =
      let result := graph.suffix.denote (.cons word input) heap
      some (encodeResult p result.1 result.2) := by
  change (lower p graph).runBlock evalOp (encodeEntry p guard input initial) (fuel + 1)
    (joinBlock p graph) ((encodeResult p word heap).append (encodeEntry p guard input initial)) = _
  rw [Cfg.runBlock, join_eval]

theorem lower_run (p : Profile) (graph : Graph args) (guard : Bool) (input : Tuple (Val p.cells) args)
    (initial : Heap p.cells) (fuel : Nat) :
    (lower p graph).run evalOp fuel (encodeEntry p guard input initial) =
      if fuel < 3 then none else
        let result := graph.denote guard input initial
        some (encodeResult p result.1 result.2) := by
  rcases fuel with _ | fuel
  · rfl
  rw [run_entry]
  rcases fuel with _ | fuel
  · rfl
  rw [run_arm, graph.merge.predecessor_slot]
  rcases fuel with _ | fuel
  · rfl
  rw [run_join]
  exact (ite_eq_right (by omega : ¬ (fuel + 1 + 1 + 1 < 3))).symm

theorem encodeResult_injective (p : Profile) :
    Function.Injective (fun result : Word × Heap p.cells => encodeResult p result.1 result.2) := by
  intro lhs rhs equal
  refine Prod.ext (congrArg (fun env : Env (resultTypes p) => env.get .here) equal) ?_
  funext index
  have cell := congrArg (fun env : Env (resultTypes p) => env.get (.there (cellVar index))) equal
  change (encodeHeap lhs.2).get (cellVar index) = (encodeHeap rhs.2).get (cellVar index) at cell
  rwa [encodeHeap_get, encodeHeap_get] at cell

theorem returns_iff (p : Profile) (graph : Graph args) (guard : Bool) (input : Tuple (Val p.cells) args)
    (initial : Heap p.cells) (word : Word) (final : Heap p.cells) :
    graph.Returns guard input initial word final ↔ Returns p graph guard input initial word final := by
  rw [graph.returns_iff_denote]
  constructor
  · intro returned
    refine ⟨3, ?_⟩
    rw [lower_run, returned]
    rfl
  · rintro ⟨fuel, returned⟩
    rw [lower_run] at returned
    by_cases short : fuel < 3
    · rw [ite_eq_left short] at returned
      cases returned
    · rw [ite_eq_right short] at returned
      exact encodeResult_injective p (Option.some.inj returned)

theorem equation_satisfaction {P : Diamond.Institution.Signature} (p : Profile) (e : Diamond.Institution.Equation P)
    (input : Tuple (Val p.cells) P.args) :
    (∀ guard initial, observe p e.lhs guard input initial = observe p e.rhs guard input initial) ↔
      e.Holds ⟨p.cells, input⟩ := by
  constructor
  · intro same guard initial
    have observed := same guard initial
    simp only [observe, lower_run, Nat.lt_irrefl, ite_false] at observed
    exact encodeResult_injective p (Option.some.inj observed)
  · intro same guard initial
    simp only [observe, lower_run, Nat.lt_irrefl, ite_false]
    exact congrArg (fun result : Word × Heap p.cells => some (encodeResult p result.1 result.2))
      (same guard initial)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Proofs
