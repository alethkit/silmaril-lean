module

public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.Thms
import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA

open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes
open Diamond (Model Val ValueSort dataPorts)
open Diamond.LambdaSSA (Atom Code Primitive encodePort encodeTuple initialContext inputEnv instruction
  instruction_deterministic portCode)
open Diamond.Arms
open Diamond.Arms.Sequential.LambdaSSA
open Diamond.Arms.LambdaSSA (resultCode)
open Loop.LambdaSSA.Generic (packed unpackContext unpackEnv unpack_typed unpack_eval)
open RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u,v} Data} {σ : Type x}
variable {inputs middle results : List (ValueSort Data)}
variable {firstSigs secondSigs : List (List (Diamond.Ty Data))}

private theorem inputIndex_head (n : Nat) : inputIndex (n + 1) 0 = 1 + 2 * n := by
  simp [inputIndex, Nat.mul_succ]
  omega

private theorem inputIndex_tail (n i : Nat) : inputIndex (n + 1) (i + 1) = inputIndex n i := by
  simp [inputIndex]

private theorem unpack_shift (i n : Nat) : i + 2 * (n + 1) = (i + 2) + 2 * n := by omega

/-- An existing binding moves past both binders introduced by each split. -/
private theorem unpack_retains_type (ports : List (Diamond.Ty Data))
    {context : List (Code Data)} {i : Nat} {A : Code Data}
    (typed : At (packed ports :: context) i A) :
    At (unpackContext context ports) (i + 2 * ports.length) A := by
  induction ports generalizing context i with
  | nil => exact typed
  | cons p rest ih =>
    have shifted : At (packed rest :: portCode p :: packed (p :: rest) :: context) (i + 2) A := typed
    rw [List.length_cons, unpack_shift]
    exact ih shifted

private theorem input_rename (ports : List (Diamond.Ty Data)) (context : List (Code Data)) :
    Ren (ports.map portCode) (unpackContext context ports) (inputIndex ports.length) := by
  induction ports generalizing context with
  | nil => intro i A typed; simp [At] at typed
  | cons p rest ih =>
    intro i A typed
    cases i with
    | zero =>
      have atHead : At (packed rest :: portCode p :: packed (p :: rest) :: context) 1 A := typed
      rw [List.length_cons, inputIndex_head]
      exact unpack_retains_type rest atHead
    | succ i =>
      rw [List.length_cons, inputIndex_tail]
      exact ih _ (show At (rest.map portCode) i A from typed)

variable (m : Model.{u,v,w} Op)

private theorem unpack_retains_value {ports : List (Diamond.Ty Data)} (values : Tuple (Val m.value) ports)
    (captured : Env (Atom m)) (i : Nat) :
    unpackEnv m values captured (i + 2 * ports.length) = extend captured (encodeTuple m values) i := by
  induction values generalizing captured i with
  | nil => rfl
  | cons x rest ih =>
    rw [List.length_cons, unpack_shift]
    exact ih (extend (extend captured (encodeTuple m (.cons x rest))) (encodePort m x)) (i + 2)

private theorem input_rename_env {ports : List (Diamond.Ty Data)} (values : Tuple (Val m.value) ports)
    (captured : Env (Atom m)) (i : Nat) :
    unpackEnv m values captured (inputIndex ports.length i) = inputEnv m values i := by
  induction values generalizing captured i with
  | nil => rfl
  | cons x rest ih =>
    cases i with
    | zero =>
      rw [List.length_cons, inputIndex_head]
      exact unpack_retains_value m rest
        (extend (extend captured (encodeTuple m (.cons x rest))) (encodePort m x)) 1
    | succ i =>
      rw [List.length_cons, inputIndex_tail]
      exact ih _ i

variable (g : Sequential.Graph Op inputs middle results firstSigs secondSigs)

theorem lower_hasType : (lower g).HasType (initialContext inputs) [resultCode results] := by
  apply (Diamond.Arms.LambdaSSA.lower_hasType g.first).linkExits
  intro i A atExit
  cases i with
  | zero =>
    have equal : resultCode middle = A := Option.some.inj atExit
    subst A
    exact unpack_typed (dataPorts middle) ((Diamond.Arms.LambdaSSA.lower_hasType g.second).renameVars
      (by simpa only [dataPorts, List.length_map] using input_rename (dataPorts middle) (initialContext inputs)))
  | succ i => simp [At] at atExit

theorem continuation_eval (joined : Tuple (Val m.value) (dataPorts middle)) (captured : Env (Atom m))
    (start : σ) :
    Semantics.Region.Eval (instruction m) (extend captured (encodeTuple m joined)) (continuation g)
      start 0 (encodeTuple m (g.second.denote m joined)) start := by
  have second := (Diamond.Arms.LambdaSSA.lower_eval_iff g.second m joined start start 0
    (encodeTuple m (g.second.denote m joined))).mpr ⟨rfl, rfl, rfl⟩
  apply unpack_eval m joined captured
  exact second.renameVars (by simpa only [dataPorts, List.length_map] using input_rename_env m joined captured)

variable (entry : Tuple (Val m.value) (dataPorts inputs))

private theorem lower_eval_denote (start : σ) :
    Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower g) start
      0 (encodeTuple m (g.denote m entry)) start := by
  let joined := g.first.denote m entry
  have first := (Diamond.Arms.LambdaSSA.lower_eval_iff g.first m entry start start 0
    (encodeTuple m joined)).mpr ⟨rfl, rfl, rfl⟩
  have next := continuation_eval m g joined (inputEnv m entry) start
  exact .cfg first (.step (next := 1) (Nat.zero_lt_succ 0)
    (next.renameLabels (fun i => 1 + i)) (.exit (Nat.le_refl 1)))

theorem lower_eval_iff (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower g) start label payload finish ↔
      label = 0 ∧ payload = encodeTuple m (g.denote m entry) ∧ finish = start := by
  constructor
  · intro run
    exact run.deterministic (instruction_deterministic m) (lower_eval_denote m g entry start)
  · rintro ⟨rfl, rfl, same⟩
    subst finish
    exact lower_eval_denote m g entry start

theorem returns_iff (start : σ) (result : Tuple (Val m.value) (dataPorts results)) :
    g.Returns m entry result ↔
      Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower g) start
        0 (encodeTuple m result) start := by
  rw [lower_eval_iff m g entry]
  constructor
  · rintro ⟨joined, first, second⟩
    obtain rfl := (g.first.returns_iff_denote m entry joined).mp first
    exact ⟨rfl, congrArg (encodeTuple m)
      ((g.second.returns_iff_denote m (g.first.denote m entry) result).mp second).symm, rfl⟩
  · rintro ⟨_, equal, _⟩
    let joined := g.first.denote m entry
    refine ⟨joined, (g.first.returns_iff_denote m entry joined).mpr rfl, ?_⟩
    apply (Diamond.Arms.LambdaSSA.returns_iff g.second m joined start result).mpr
    exact (Diamond.Arms.LambdaSSA.lower_eval_iff g.second m joined start start 0 (encodeTuple m result)).mpr
      ⟨rfl, equal, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA
