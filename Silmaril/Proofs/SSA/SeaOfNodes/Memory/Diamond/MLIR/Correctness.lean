module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Proofs

open RVSDG (Locals Origin Port Tuple)
open SeaOfNodes.Diamond (Projection Slot)
open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.Pure (Code Operands)
open Silmaril.MLIR.CF (Cfg Frame Terminator)

variable {args : List ValueSort} {past : List (List ValueSort)} {Γ : List Width} {version : Nat}

private theorem address_cases (address : Address 2) : address = firstCell ∨ address = secondCell :=
  Fin.cases (.inl rfl) (fun i => .inr (congrArg Fin.succ (Fin.eq_zero i))) address

private theorem load_select (address : Address 2) (heap : Heap 2) :
    selectWord (encodeValue (sort := .address) address) (heap secondCell) (heap firstCell) =
      heap.read address := by
  rcases address_cases address with rfl | rfl <;> rfl

private theorem store_select (address : Address 2) (heap : Heap 2) (value : Word) :
    selectWord (encodeValue (sort := .address) address) (heap firstCell) value =
        (heap.write address value) firstCell ∧
      selectWord (encodeValue (sort := .address) address) value (heap secondCell) =
        (heap.write address value) secondCell := by
  rcases address_cases address with rfl | rfl <;> exact ⟨rfl, rfl⟩

private def Matches (route : Routing args past Γ) (env : Env Γ)
    (input : Tuple (Val 2) args) (locals : Locals (Val 2) past) : Prop :=
  ∀ {sort} (wire : Origin args past sort), env.get (route wire) = encodeValue (readValue wire input locals)

private def HeapAgrees (refs : HeapRefs Γ) (env : Env Γ) (heap : Heap 2) : Prop :=
  env.get refs.first = heap firstCell ∧ env.get refs.second = heap secondCell

private theorem afterLoad_match {route : Routing args past Γ} {env : Env Γ}
    {input : Tuple (Val 2) args} {locals : Locals (Val 2) past}
    (matched : Matches route env input locals) (word : Word) :
    Matches route.afterLoad (.cons word env) input (.cons word .nil, locals) := by
  intro sort wire
  cases wire with
  | arg p => exact matched (.arg p)
  | output i p =>
    refine Fin.cases (motive := fun j => ∀ port : Port ([.word] :: past)[j] sort,
      (Env.cons (w := i64) word env).get (route.afterLoad (.output j port)) =
        encodeValue (readValue (Origin.output (past := [.word] :: past) j port) input
          (Tuple.cons (F := Val 2) (t := .word) word .nil, locals))) ?_ ?_ i p
    · intro port
      cases port with
      | head => rfl
      | tail impossible => cases impossible
    · intro j port
      exact matched (.output j port)

private theorem eval_lowerBody {Term : List Width → Type} {α : Type}
    (body : Memory.Body args past version) (finish : Finish Term)
    (interpret : ∀ {Δ}, Term Δ → Env Δ → α) (pack : Word → Heap 2 → α)
    (finishLaw : ∀ {Δ} (word : Var Δ i64) (refs : HeapRefs Δ) (env : Env Δ) (heap : Heap 2),
      HeapAgrees refs env heap → interpret (finish word refs) env = pack (env.get word) heap)
    (route : Routing args past Γ) (refs : HeapRefs Γ) (env : Env Γ)
    (input : Tuple (Val 2) args) (locals : Locals (Val 2) past) (heap : Heap 2)
    (matched : Matches route env input locals) (heapMatches : HeapAgrees refs env heap) :
    (lowerBody finish body route refs).eval evalOp interpret env =
      let result := body.denote input locals heap
      pack result.1 result.2 := by
  induction body generalizing Γ heap with
  | ret _ word =>
    change interpret (finish (route word) refs) env = pack (readValue word input locals) heap
    exact (finishLaw (route word) refs env heap heapMatches).trans
      (congrArg (fun value => pack value heap) (matched word))
  | load _ address rest ih =>
    let loaded := heap.read (readValue address input locals)
    have value : selectWord (env.get (route address)) (env.get refs.second) (env.get refs.first) = loaded := by
      rw [matched address, heapMatches.2, heapMatches.1]
      exact load_select _ _
    change (lowerBody finish rest route.afterLoad (refs.weaken i64)).eval evalOp interpret
      (.cons (selectWord (env.get (route address)) (env.get refs.second) (env.get refs.first)) env) = _
    rw [value]
    exact ih route.afterLoad (refs.weaken i64) (.cons loaded env) (.cons loaded .nil, locals)
      heap (afterLoad_match matched loaded) ⟨heapMatches.1, heapMatches.2⟩
  | store _ address word rest ih =>
    let target := readValue address input locals
    let value := readValue word input locals
    have selectFirst :
        selectWord (env.get (route address)) (env.get refs.first) (env.get (route word)) =
          (heap.write target value) firstCell := by
      rw [matched address, heapMatches.1, matched word]
      exact (store_select target heap value).1
    have selectSecond :
        selectWord (env.get (route address)) (env.get (route word)) (env.get refs.second) =
          (heap.write target value) secondCell := by
      rw [matched address, matched word, heapMatches.2]
      exact (store_select target heap value).2
    change (lowerBody finish rest (Routing.weaken i64 (Routing.weaken i64 route))
      ⟨.there .here, .here⟩).eval evalOp interpret
      (.cons (selectWord (env.get (route address)) (env.get (route word)) (env.get refs.second))
        (.cons (selectWord (env.get (route address)) (env.get refs.first) (env.get (route word))) env)) = _
    rw [selectFirst, selectSecond]
    exact ih (Routing.weaken i64 (Routing.weaken i64 route)) ⟨.there .here, .here⟩ _ locals
      (heap.write target value) (fun wire => matched wire) ⟨rfl, rfl⟩

private theorem scalars_match (input : Tuple (Val 2) args) {sort : ValueSort} (p : Port args sort) :
    (encodeScalars input).get (argVar p) = encodeValue (input.get p) := by
  induction p with
  | head => cases input; rfl
  | tail _ ih => cases input with | cons _ rest => exact ih rest

private theorem entry_match (guard : Bool) (input : Tuple (Val 2) args) (heap : Heap 2) :
    Matches (entryRoute args) (encodeEntry guard input heap) input PUnit.unit := by
  intro sort wire
  cases wire with
  | arg port => exact scalars_match input port
  | output i _ => exact i.elim0

private theorem join_match (guard : Bool) (input : Tuple (Val 2) args) (heap : Heap 2)
    (word : Word) (final : Heap 2) :
    Matches (joinRoute args) ((encodeResult word final).append (encodeEntry guard input heap))
      (.cons word input) PUnit.unit := by
  intro sort wire
  cases wire with
  | arg port =>
    cases port with
    | head => rfl
    | tail p => exact scalars_match input p
  | output i _ => exact i.elim0

private theorem pack_operands (word : Var Γ i64) (refs : HeapRefs Γ) (env : Env Γ) (heap : Heap 2)
    (matched : HeapAgrees refs env heap) :
    (resultOperands word refs).eval env = encodeResult (env.get word) heap := by
  change Env.cons (env.get word) (.cons (env.get refs.first) (.cons (env.get refs.second) .nil)) = _
  rw [matched.1, matched.2]
  rfl

private def joinFrame (word : Word) (heap : Heap 2) : Frame Label :=
  ⟨.join, encodeResult word heap⟩

private theorem arm_eval (graph : Graph args) (slot : Slot) (guard : Bool)
    (input : Tuple (Val 2) args) (initial : Heap 2) :
    (armBlock graph slot).eval evalOp (fun term env => term.eval env) (encodeEntry guard input initial) =
      let selected := (graph.arm (graph.merge.predecessor slot)).denote input initial
      Sum.inl (joinFrame selected.1 selected.2) := by
  refine eval_lowerBody (graph.arm (graph.merge.predecessor slot))
    (fun word heap => Terminator.br ⟨Label.join, resultOperands word heap⟩)
    (fun term env => term.eval env) (fun word heap => Sum.inl (joinFrame word heap)) ?_
    (entryRoute args) (entryHeap args) _ input PUnit.unit initial
    (entry_match guard input initial) ⟨rfl, rfl⟩
  intro Δ word refs env heap matchHeap
  exact congrArg (fun values => Sum.inl (Frame.mk (Label.join) values))
    (pack_operands word refs env heap matchHeap)

private theorem join_eval (graph : Graph args) (guard : Bool) (input : Tuple (Val 2) args)
    (initial : Heap 2) (word : Word) (heap : Heap 2) :
    (joinBlock graph).eval evalOp (fun term env => term.eval env)
        ((encodeResult word heap).append (encodeEntry guard input initial)) =
      let result := graph.suffix.denote (.cons word input) heap
      Sum.inr (encodeResult result.1 result.2) := by
  refine eval_lowerBody graph.suffix (fun word heap => Terminator.ret (resultOperands word heap))
    (fun term env => term.eval env) (fun word heap => Sum.inr (encodeResult word heap)) ?_
    (joinRoute args) (joinHeap args) _ (.cons word input) PUnit.unit heap (join_match guard input initial word heap) ⟨rfl, rfl⟩
  intro Δ result refs env final matchHeap
  exact congrArg Sum.inr (pack_operands result refs env final matchHeap)

private def armFrame (slot : Slot) : Frame Label := ⟨.arm slot, .nil⟩

private theorem entry_eval (graph : Graph args) (guard : Bool) (input : Tuple (Val 2) args)
    (initial : Heap 2) :
    (lower graph).entry.eval evalOp (fun term env => term.eval env) (encodeEntry guard input initial) =
      Sum.inl (armFrame (graph.merge.slot (Projection.ofBool guard))) := by
  change Sum.inl (if (BitVec.ofBool guard).getLsbD 0 then armFrame (graph.merge.slot .onTrue)
    else armFrame (graph.merge.slot .onFalse)) = _
  rw [BitVec.getLsbD_ofBool]
  cases guard <;> rfl

private theorem run_entry (graph : Graph args) (guard : Bool) (input : Tuple (Val 2) args)
    (initial : Heap 2) (fuel : Nat) :
    (lower graph).run evalOp (fuel + 1) (encodeEntry guard input initial) =
      (lower graph).runFrom evalOp fuel (encodeEntry guard input initial)
        (armFrame (graph.merge.slot (Projection.ofBool guard))) := by
  rw [Cfg.run, Cfg.runBlock, entry_eval]
  rfl

private theorem run_arm (graph : Graph args) (slot : Slot) (guard : Bool) (input : Tuple (Val 2) args)
    (initial : Heap 2) (fuel : Nat) :
    (lower graph).runFrom evalOp (fuel + 1) (encodeEntry guard input initial) (armFrame slot) =
      let selected := (graph.arm (graph.merge.predecessor slot)).denote input initial
      (lower graph).runFrom evalOp fuel (encodeEntry guard input initial) (joinFrame selected.1 selected.2) := by
  change (lower graph).runBlock evalOp (encodeEntry guard input initial) (fuel + 1)
    (armBlock graph slot) (encodeEntry guard input initial) = _
  rw [Cfg.runBlock, arm_eval]
  rfl

private theorem run_join (graph : Graph args) (guard : Bool) (input : Tuple (Val 2) args)
    (initial : Heap 2) (word : Word) (heap : Heap 2) (fuel : Nat) :
    (lower graph).runFrom evalOp (fuel + 1) (encodeEntry guard input initial) (joinFrame word heap) =
      let result := graph.suffix.denote (.cons word input) heap
      some (encodeResult result.1 result.2) := by
  change (lower graph).runBlock evalOp (encodeEntry guard input initial) (fuel + 1)
    (joinBlock graph) ((encodeResult word heap).append (encodeEntry guard input initial)) = _
  rw [Cfg.runBlock, join_eval]

theorem lower_run (graph : Graph args) (guard : Bool) (input : Tuple (Val 2) args)
    (initial : Heap 2) (fuel : Nat) :
    (lower graph).run evalOp fuel (encodeEntry guard input initial) =
      if fuel < 3 then none else
        let result := graph.denote guard input initial
        some (encodeResult result.1 result.2) := by
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

private theorem encodeResult_inj {word other : Word} {heap another : Heap 2}
    (equal : encodeResult word heap = encodeResult other another) :
    (word, heap) = (other, another) := by
  refine Prod.ext (congrArg (fun env : Env resultTypes => env.get .here) equal) ?_
  funext address
  rcases address_cases address with rfl | rfl
  · exact congrArg (fun env : Env resultTypes => env.get (.there .here)) equal
  · exact congrArg (fun env : Env resultTypes => env.get (.there (.there .here))) equal

theorem returns_iff (graph : Graph args) (guard : Bool) (input : Tuple (Val 2) args)
    (initial : Heap 2) (word : Word) (final : Heap 2) :
    graph.Returns guard input initial word final ↔ Returns graph guard input initial word final := by
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
      exact encodeResult_inj (Option.some.inj returned)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Proofs
