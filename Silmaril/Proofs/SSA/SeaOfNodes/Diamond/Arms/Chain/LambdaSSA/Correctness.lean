module

public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA

open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes
open Diamond (Model Slot Val ValueSort dataPorts)
open Diamond.Arms (Chain)
open Diamond.Arms.Chain.LambdaSSA
open Diamond.Arms.LambdaSSA (resultCode)
open Diamond.Arms.Sequential.LambdaSSA (link_hasType link_eval_iff)
open Diamond.LambdaSSA (Atom Code encodeTuple encodeTuple_injective initialContext inputEnv
  instruction instruction_deterministic portCode)
open RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u,v} Data} {σ : Type x}
variable {inputs results : List (ValueSort Data)}

theorem edge_stage (chain : Chain Op inputs results) (stage : Fin chain.length) (slot : Slot) :
    (edge chain stage slot).source.1 = stage := by
  induction chain with
  | nil => exact stage.elim0
  | cons head tail ih =>
    refine Fin.cases (motive := fun i => (edge (.cons head tail) i slot).source.1 = i) rfl
      (fun i => ?_) stage
    exact congrArg Fin.succ (ih i)

theorem lower_hasType (chain : Chain Op inputs results) :
    (lower chain).HasType (initialContext inputs) [resultCode results] := by
  induction chain with
  | nil => exact .br (ℓ := 0) rfl (PhiView.packTerm_hasType (identityArgs _))
  | cons head _ ih => exact link_hasType (Diamond.Arms.LambdaSSA.lower_hasType head) ih

variable (m : Model.{u,v,w} Op)

private theorem pack_input_eval {ports : List (Diamond.Ty Data)} {context : List (Code Data)}
    (values : Tuple (Val m.value) ports) (env : Env (Atom m))
    (args : PhiView.Arguments context (ports.map portCode))
    (reads : ∀ i, env (args i).val = inputEnv m values i) (start : σ) :
    Semantics.Tm.Eval (instruction m) env (PhiView.packTerm args) start (encodeTuple m values) start := by
  induction values with
  | nil => exact .unit
  | cons value rest ih =>
    exact .pair (Semantics.Tm.Eval.var_of_eq (reads ⟨0, Nat.zero_lt_succ _⟩))
      (ih (fun i => args i.succ) (fun i => reads i.succ))

theorem lower_eval_iff (chain : Chain Op inputs results) (entry : Tuple (Val m.value) (dataPorts inputs))
    (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower chain) start label payload finish ↔
      label = 0 ∧ payload = encodeTuple m (chain.denote m entry) ∧ finish = start := by
  induction chain generalizing finish label payload with
  | nil =>
    rename_i inputs
    have run : Semantics.Region.Eval (instruction m) (inputEnv m entry)
        (lower (.nil : Chain Op inputs inputs)) start 0 (encodeTuple m entry) start := by
      rw [lower]
      exact .br (pack_input_eval m entry _ (identityArgs _) (fun _ => rfl) start)
    constructor
    · intro observed
      exact observed.deterministic (instruction_deterministic m) run
    · rintro ⟨rfl, rfl, same⟩
      subst finish
      exact run
  | cons head tail ih =>
    let joined := head.denote m entry
    have beforeRun := (Diamond.Arms.LambdaSSA.lower_eval_iff head m entry start start 0
      (encodeTuple m joined)).mpr ⟨rfl, rfl, rfl⟩
    have afterRun := (ih joined start 0 (encodeTuple m (tail.denote m joined))).mpr ⟨rfl, rfl, rfl⟩
    exact link_eval_iff m beforeRun afterRun label payload finish

private theorem returns_iff_denote (chain : Chain Op inputs results) (entry : Tuple (Val m.value) (dataPorts inputs))
    (result : Tuple (Val m.value) (dataPorts results)) :
    chain.Returns m entry result ↔ chain.denote m entry = result := by
  induction chain with
  | nil => rfl
  | cons head tail ih =>
    constructor
    · rintro ⟨joined, before, after⟩
      obtain rfl := (head.returns_iff_denote m entry joined).mp before
      exact (ih _ _).mp after
    · intro same
      refine ⟨head.denote m entry, (head.returns_iff_denote m entry _).mpr rfl, ?_⟩
      exact (ih _ _).mpr same

theorem returns_iff (chain : Chain Op inputs results) (entry : Tuple (Val m.value) (dataPorts inputs))
    (start : σ) (result : Tuple (Val m.value) (dataPorts results)) :
    chain.Returns m entry result ↔
      Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower chain) start
        0 (encodeTuple m result) start := by
  rw [returns_iff_denote m chain entry, lower_eval_iff m chain entry]
  exact ⟨fun same => ⟨rfl, congrArg (encodeTuple m) same.symm, rfl⟩,
    fun eval => (encodeTuple_injective m results eval.2.1).symm⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA
