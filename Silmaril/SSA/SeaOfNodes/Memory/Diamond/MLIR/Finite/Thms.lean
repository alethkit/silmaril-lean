module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Body
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Correctness

/-! Exact finite execution of the indexed scalar heap lowering. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite

open RVSDG (Locals Port Tuple)
open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.Pure (Code)
open Silmaril.MLIR.SCF.For (weakenVar)
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution renaming
  Signature → EntrySignature, Equation → NativeEquation

variable {args : List ValueSort} {P : EntrySignature}
variable {p : Profile} {past : List (List ValueSort)} {version : Nat}
variable {Γ Δ : List Width} {w : Width}

theorem get_appendVar (ref : Var Γ w) (arguments : Env Γ) (suffix : Env Δ) :
    (arguments.append suffix).get (appendVar Δ ref) = arguments.get ref :=
  Proofs.get_appendVar ref arguments suffix

theorem get_weakenVar (arguments : Env Δ) (input : Env Γ) (ref : Var Γ w) :
    (arguments.append input).get (weakenVar ref Δ) = input.get ref :=
  Proofs.get_weakenVar arguments input ref

theorem get_encodeHeap_cellVar {cells : Nat} (heap : Heap cells) (index : Address cells) :
    (encodeHeap heap).get (cellVar index) = heap index :=
  Proofs.get_encodeHeap_cellVar heap index

theorem get_encodeScalars_argVar (input : Tuple (Val p.cells) args) {sort : ValueSort} (port : Port args sort) :
    (encodeScalars p input).get (argVar port) = encodeValue p (input.get port) :=
  Proofs.get_encodeScalars_argVar input port

theorem eval_heapOperands {cells : Nat} (refs : HeapRefs cells Γ) (env : Env Γ)
    (heap : Heap cells) (ok : ∀ index, env.get (refs index) = heap index) :
    (heapOperands refs).eval env = encodeHeap heap :=
  Proofs.eval_heapOperands refs env heap ok

theorem eval_resultOperands (word : Var Γ i64) (refs : HeapRefs p.cells Γ) (env : Env Γ)
    (heap : Heap p.cells) (ok : HeapAgrees refs env heap) :
    (resultOperands (p := p) word refs).eval env = encodeResult p (env.get word) heap :=
  Proofs.eval_resultOperands word refs env heap ok

/-- An emitted ordered memory body agrees with native evaluation for any
terminator that consumes its returned word and updated heap. -/
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
      pack result.1 result.2 :=
  Proofs.eval_lowerBody body finish interpret pack finish_ok route refs env input locals heap matched heap_ok

/-- Every budget that reaches the suffix returns the native word and all
cells in index order. Smaller budgets have no return. -/
theorem lower_run (p : Profile) (graph : Graph args) (guard : Bool) (input : Tuple (Val p.cells) args)
    (initial : Heap p.cells) (fuel : Nat) :
    (lower p graph).run evalOp fuel (encodeEntry p guard input initial) =
      if fuel < 3 then none else
        let result := graph.denote guard input initial
        some (encodeResult p result.1 result.2) :=
  Proofs.lower_run p graph guard input initial fuel

theorem encodeResult_injective (p : Profile) :
    Function.Injective (fun result : Word × Heap p.cells => encodeResult p result.1 result.2) :=
  Proofs.encodeResult_injective p

/-- Preserve and reflect the exact finite word and whole initialized heap
at the chosen cell count, for either source guard. -/
theorem returns_iff (p : Profile) (graph : Graph args) (guard : Bool) (input : Tuple (Val p.cells) args)
    (initial : Heap p.cells) (word : Word) (final : Heap p.cells) :
    graph.Returns guard input initial word final ↔ Returns p graph guard input initial word final :=
  Proofs.returns_iff p graph guard input initial word final

/-- Compare emitted CFGs at any checked profile with the native equation at
that cell count and typed valuation. -/
theorem equation_satisfaction (p : Profile) (e : NativeEquation P)
    (input : Tuple (Val p.cells) P.args) :
    (∀ guard initial, observe p e.lhs guard input initial = observe p e.rhs guard input initial) ↔
      e.Holds ⟨p.cells, input⟩ :=
  Proofs.equation_satisfaction p e input

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite
