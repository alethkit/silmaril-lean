module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Proofs

open RVSDG (Locals Origin Port Tuple)
open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.Pure (Code i1)

variable {p : Profile} {args : List ValueSort} {past : List (List ValueSort)}
variable {Γ Δ : List Width} {version : Nat}

@[expose] def Matches (route : Routing p args past Γ) (env : Env Γ)
    (input : Tuple (Val p.cells) args) (locals : Locals (Val p.cells) past) : Prop :=
  ∀ {sort} (wire : Origin args past sort),
    env.get (route wire) = encodeValue p (readValue wire input locals)

@[expose] def HeapAgrees (refs : HeapRefs p.cells Γ) (env : Env Γ) (heap : Heap p.cells) : Prop :=
  ∀ index, env.get (refs index) = heap index

private def Preserves (widen : Rename Γ Δ) (env : Env Γ) (next : Env Δ) : Prop :=
  ∀ {w} (ref : Var Γ w), next.get (widen ref) = env.get ref

private theorem encodeAddress_eq_iff (a b : Address p.cells) :
    encodeAddress p a = encodeAddress p b ↔ a = b := by
  constructor
  · intro equal
    apply Fin.ext
    simpa only [encodeAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a.isLt.trans_le p.fits),
      Nat.mod_eq_of_lt (b.isLt.trans_le p.fits)] using congrArg BitVec.toNat equal
  · exact congrArg (encodeAddress p)

-- This is the environment after the three let bindings in selectCell.
private def selectedEnv (env : Env Γ) (index : Address p.cells)
    (address : Var Γ p.addressWidth) (onMatch otherwise : Var Γ i64) :
    Env (i64 :: i1 :: p.addressWidth :: Γ) :=
  let bits := encodeAddress p index
  let test := BitVec.ofBool (decide (env.get address = bits))
  .cons (MLIR.selectWord test (env.get onMatch) (env.get otherwise)) (.cons test (.cons bits env))

private theorem selected_get (env : Env Γ) (index target : Address p.cells)
    (address : Var Γ p.addressWidth) (onMatch otherwise : Var Γ i64)
    (address_ok : env.get address = encodeAddress p target) :
    (selectedEnv env index address onMatch otherwise).get .here =
      if target = index then env.get onMatch else env.get otherwise := by
  change MLIR.selectWord (BitVec.ofBool (decide (env.get address = encodeAddress p index)))
    (env.get onMatch) (env.get otherwise) = _
  rw [address_ok]
  by_cases same : target = index
  · simp [same, MLIR.selectWord]
  · have encoded : encodeAddress p target ≠ encodeAddress p index :=
      fun equal => same ((encodeAddress_eq_iff target index).1 equal)
    simp [encoded, same, MLIR.selectWord]

private theorem eval_loadCells {Term : List Width → Type} {α : Type}
    (indices : List (Address p.cells)) (address : Var Γ p.addressWidth)
    (refs : HeapRefs p.cells Γ) (fallback : Var Γ i64)
    (finish : ∀ {Δ}, Rename Γ Δ → Var Δ i64 → Code Op Term Δ)
    (interpret : ∀ {Δ}, Term Δ → Env Δ → α) (pack : Word → α)
    (env : Env Γ) (target : Address p.cells) (heap : Heap p.cells)
    (address_ok : env.get address = encodeAddress p target) (heap_ok : HeapAgrees refs env heap)
    (finish_ok : ∀ {Δ} (widen : Rename Γ Δ) (word : Var Δ i64) (next : Env Δ),
      Preserves widen env next → (finish widen word).eval evalOp interpret next = pack (next.get word)) :
    (loadCells indices address refs fallback finish).eval evalOp interpret env =
      pack (if target ∈ indices then heap target else env.get fallback) := by
  induction indices generalizing Γ with
  | nil => simpa [loadCells] using finish_ok (fun ref => ref) fallback env (fun _ => rfl)
  | cons index rest ih =>
    let next := selectedEnv env index address (refs index) fallback
    change (loadCells rest (underSelect address) (fun j => underSelect (refs j)) .here
      (fun widen word => finish (fun ref => widen (underSelect ref)) word)).eval evalOp interpret next = _
    have scanned := ih (underSelect address) (fun j => underSelect (refs j)) .here
      (fun widen word => finish (fun ref => widen (underSelect ref)) word)
      next address_ok heap_ok
      (fun widen word after ok => finish_ok (fun ref => widen (underSelect ref)) word after
        (fun ref => ok (underSelect ref)))
    refine scanned.trans ?_
    rw [selected_get env index target address (refs index) fallback address_ok, heap_ok index]
    by_cases present : target ∈ rest
    · simp [present]
    · by_cases here : target = index <;> simp [List.mem_cons, present, here]

private theorem update_heap_agrees (refs : HeapRefs p.cells Γ) (env : Env Γ)
    (heap : Heap p.cells) (index : Address p.cells) (ref : Var Γ i64) (value : Word)
    (heap_ok : HeapAgrees refs env heap) (value_ok : env.get ref = value) :
    HeapAgrees (Function.update refs index ref) env (heap.write index value) := by
  intro cell
  by_cases same : cell = index
  · subst cell
    simpa only [Heap.write, Function.update_self] using value_ok
  · simpa only [Heap.write, Function.update_of_ne same] using heap_ok cell

private theorem eval_storeCells {Term : List Width → Type} {α : Type}
    (indices : List (Address p.cells)) (address : Var Γ p.addressWidth)
    (word : Var Γ i64) (refs : HeapRefs p.cells Γ)
    (finish : ∀ {Δ}, Rename Γ Δ → HeapRefs p.cells Δ → Code Op Term Δ)
    (interpret : ∀ {Δ}, Term Δ → Env Δ → α) (pack : Heap p.cells → α)
    (env : Env Γ) (target : Address p.cells) (value : Word) (heap : Heap p.cells)
    (address_ok : env.get address = encodeAddress p target) (word_ok : env.get word = value)
    (heap_ok : HeapAgrees refs env heap)
    (finish_ok : ∀ {Δ} (widen : Rename Γ Δ) (nextRefs : HeapRefs p.cells Δ) (next : Env Δ)
      (final : Heap p.cells), Preserves widen env next → HeapAgrees nextRefs next final →
        (finish widen nextRefs).eval evalOp interpret next = pack final) :
    (storeCells indices address word refs finish).eval evalOp interpret env =
      pack (if target ∈ indices then heap.write target value else heap) := by
  induction indices generalizing Γ heap with
  | nil => simpa [storeCells] using finish_ok (fun ref => ref) refs env heap (fun _ => rfl) heap_ok
  | cons index rest ih =>
    let next := selectedEnv env index address word (refs index)
    let nextRefs : HeapRefs p.cells (i64 :: i1 :: p.addressWidth :: Γ) :=
      Function.update (fun j => underSelect (refs j)) index .here
    let updated := heap.write index (if target = index then value else heap index)
    have cell_ok : next.get .here = if target = index then value else heap index := by
      rw [selected_get env index target address word (refs index) address_ok, word_ok, heap_ok index]
    have next_ok : HeapAgrees nextRefs next updated :=
      update_heap_agrees _ next heap index .here _ heap_ok cell_ok
    change (storeCells rest (underSelect address) (underSelect word) nextRefs
      (fun widen names => finish (fun ref => widen (underSelect ref)) names)).eval evalOp interpret next = _
    have scanned := ih (underSelect address) (underSelect word) nextRefs
      (fun widen names => finish (fun ref => widen (underSelect ref)) names)
      next updated address_ok word_ok next_ok
      (fun widen names after final ok values => finish_ok (fun ref => widen (underSelect ref))
        names after final (fun ref => ok (underSelect ref)) values)
    refine scanned.trans (congrArg pack ?_)
    by_cases here : target = index
    · subst index
      simp [updated, Heap.write, Function.update_idem]
    · have same : updated = heap := by
        simp [updated, here, Heap.write, Function.update_eq_self]
      simp [same, List.mem_cons, here]

private theorem afterLoad_match {route : Routing p args past Γ} {widen : Rename Γ Δ}
    {env : Env Γ} {next : Env Δ} {input : Tuple (Val p.cells) args}
    {locals : Locals (Val p.cells) past} {word : Var Δ i64}
    (matched : Matches route env input locals) (preserved : Preserves widen env next) :
    Matches (route.afterLoad widen word) next input (.cons (next.get word) .nil, locals) := by
  intro sort wire
  cases wire with
  | arg port => exact (preserved (route (.arg port))).trans (matched (.arg port))
  | output index port =>
    refine Fin.cases (motive := fun j => ∀ q : Port ([.word] :: past)[j] sort,
      next.get (route.afterLoad widen word (.output j q)) =
        encodeValue p (readValue (Origin.output (past := [.word] :: past) j q) input
          (Tuple.cons (F := Val p.cells) (t := .word) (next.get word) .nil, locals))) ?_ ?_ index port
    · intro q
      cases q with
      | head => rfl
      | tail impossible => cases impossible
    · intro j q
      exact (preserved (route (.output j q))).trans (matched (.output j q))

theorem eval_lowerBody {Term : List Width → Type} {α : Type}
    (body : Memory.Body args past version) (finish : Finish p Term)
    (interpret : ∀ {Δ}, Term Δ → Env Δ → α) (pack : Word → Heap p.cells → α)
    (finish_ok : ∀ {Δ} (word : Var Δ i64) (refs : HeapRefs p.cells Δ) (env : Env Δ) (heap : Heap p.cells),
      HeapAgrees refs env heap → interpret (finish word refs) env = pack (env.get word) heap)
    (route : Routing p args past Γ) (refs : HeapRefs p.cells Γ) (env : Env Γ)
    (input : Tuple (Val p.cells) args) (locals : Locals (Val p.cells) past) (heap : Heap p.cells)
    (matched : Matches route env input locals) (heap_ok : HeapAgrees refs env heap) :
    (lowerBody finish body route refs).eval evalOp interpret env =
      let result := body.denote input locals heap
      pack result.1 result.2 := by
  induction body generalizing Γ heap with
  | ret _ word =>
    exact (finish_ok (route word) refs env heap heap_ok).trans
      (congrArg (fun value => pack value heap) (matched word))
  | load _ address rest ih =>
    let next : Env (i64 :: Γ) := .cons 0 env
    let restCode : ∀ {Δ}, Rename (i64 :: Γ) Δ → Var Δ i64 → Code Op Term Δ :=
      fun widen word => lowerBody finish rest (route.afterLoad (fun ref => widen (.there ref)) word)
        (fun j => widen (.there (refs j)))
    let outcome := fun value : Word =>
      let result := rest.denote input (.cons value .nil, locals) heap
      pack result.1 result.2
    change (loadCells (List.finRange p.cells) (.there (route address)) (fun j => .there (refs j))
      .here restCode).eval evalOp interpret next = outcome (heap.read (readValue address input locals))
    have scanned := eval_loadCells (List.finRange p.cells) (.there (route address))
      (fun j => .there (refs j)) .here restCode interpret outcome next
      (readValue address input locals) heap (matched address) heap_ok (by
        intro Δ widen word after preserved
        exact ih _ _ after (.cons (after.get word) .nil, locals) heap
          (afterLoad_match matched (fun ref => preserved (.there ref)))
          (fun j => (preserved (.there (refs j))).trans (heap_ok j)))
    exact scanned.trans (congrArg outcome (ite_eq_left (List.mem_finRange (readValue address input locals))))
  | store _ address word rest ih =>
    let restCode : ∀ {Δ}, Rename Γ Δ → HeapRefs p.cells Δ → Code Op Term Δ :=
      fun widen final => lowerBody finish rest (route.rename widen) final
    let outcome := fun final : Heap p.cells =>
      let result := rest.denote input locals final
      pack result.1 result.2
    change (storeCells (List.finRange p.cells) (route address) (route word) refs restCode).eval
      evalOp interpret env = outcome (heap.write (readValue address input locals) (readValue word input locals))
    have scanned := eval_storeCells (List.finRange p.cells) (route address) (route word) refs restCode
      interpret outcome env (readValue address input locals) (readValue word input locals) heap
      (matched address) (matched word) heap_ok (by
        intro Δ widen final after memory preserved memory_ok
        exact ih _ final after locals memory (fun wire => (preserved (route wire)).trans (matched wire))
          memory_ok)
    exact scanned.trans (congrArg outcome (ite_eq_left (List.mem_finRange (readValue address input locals))))

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Proofs
