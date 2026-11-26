module

import Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Reverse.Thms
import Silmaril.Semantics.ElgotMonads.Thms
meta import Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Defs
meta import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Reverse.Defs

namespace Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Regression

open Silmaril.MLIR.Arith (Env Width)
open LambdaSSA.Acyclic.Theta.Translation
open LambdaSSA.OrderedTheta (point)
open LambdaSSA.TwoBlock.TwoExit (callCase)
open Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Elgot (iter)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

private abbrev Ty := Silmaril.Ty Unit
private abbrev Word := BitVec 8
private abbrev word : Ty := .base ()
private def width : Width := ⟨8, by decide⟩

@[reducible] private def Value : Ty → Type
  | .base _ => Word
  | .product a b => Value a × Value b
  | .unit => PUnit
  | .coprod a b => Value a ⊕ Value b
  | .empty => PEmpty

private def coerce {A B : Ty} : Isotope.Ty.Subty A B → Value A → Value B
  | .refl _ => id
  | .trans f g => coerce g ∘ coerce f
  | .product f g => fun (a,b) => (coerce f a, coerce g b)
  | .coprod f g => Sum.map (coerce f) (coerce g)
  | .empty _ => PEmpty.elim
  | .unit _ => fun _ => PUnit.unit

local instance : TypeModel Ty where
  interp := Value
  productEquiv _ _ := Equiv.refl _
  coprodEquiv _ _ := Equiv.refl _
  unitEquiv := ⟨fun _ => (), fun _ => PUnit.unit, fun _ => rfl, fun _ => rfl⟩
  emptyEquiv := ⟨PEmpty.elim, Empty.elim, (fun x => x.elim), (fun x => x.elim)⟩
  coe := coerce

private inductive Op | bump | test
  deriving DecidableEq

local instance : HasTy Op Ty := ⟨fun _ => word,
  fun | .bump => word | .test => .coprod word word⟩

local instance : HasEff Op Bool := ⟨fun | .bump => false | .test => true⟩

private abbrev Runtime := StateT Nat Part

-- The branch decision reads the incoming token. The final stopping
-- activation also writes a token. Only payload 99 selects undefinedness.
private def classify (x : Word) (token : Nat) : Option (Bool × Nat) :=
  if x = 99 then none else some (decide (token < 200), 10 * token + 7)

private def instruction : (op : Op) → Value (instrSrc op) → Runtime (Value (instrTrg op))
  | .bump, x => pure ((show Word from x) + 1)
  | .test, x => StateT.mk fun token => Part.ofOption ((classify x token).map fun (again, next) =>
    ((if again then Sum.inr x else Sum.inl x), next))

local instance : InstructionModel Op Ty Bool Runtime where
  denote := instruction
  denotePure op bottom x := by
    cases op with
    | bump => exact (show Word from x) + 1
    | test => cases (show true = false from bottom)
  denote_pure op bottom x := by
    cases op with
    | bump => rfl
    | test => cases (show true = false from bottom)

private def loop : PureTheta.Loop Op Bool word :=
  ⟨⟨.bump, rfl, rfl⟩, rfl, ⟨.test, rfl, rfl⟩⟩

private def codec : TyDen word ≃ BitVec width.val := Equiv.refl Word

private def recovered (order : Bool) : PureTheta.Reverse.Fibre (loop.compile order) :=
  (PureTheta.Reverse.recover (loop.compile order)).get
    (by simp [PureTheta.Reverse.recover_generated])

private abbrev step := Elgot.StateT.body (loop.step (σ := Nat))

private theorem classifier_call (x : Word) :
    callCase (ε := Bool) (m := Runtime) loop.decide x = instruction .test x := by
  unfold callCase LambdaSSA.TwoBlock.call
  change (instruction .test x >>= pure) >>= pure = _
  simp only [bind_pure]

private theorem step_run (x : Word) (token : Nat) :
    Elgot.StateT.body (loop.step (σ := Nat)) (x, token) = Part.ofOption ((classify x token).map fun (again, next) =>
      if again then Sum.inr (x + 1, next) else Sum.inl (x + 1, next)) := by
  unfold Elgot.StateT.body PureTheta.Loop.step
  change ((callCase (ε := Bool) (m := Runtime) loop.decide x >>= _).run token).bind _ = _
  rw [classifier_call]
  cases h : classify x token with
  | none => simp [instruction, h, Part.ofOption]
  | some result =>
    rcases result with ⟨again, next⟩
    cases again <;> simp [instruction, h, Part.ofOption, Elgot.StateT.distribute, Part.pure_eq_some]
    all_goals rfl

private theorem source_returns (order : Bool) :
    NestedTheta.Partial.observe (PureGamma.model (Φ := Op) (ε := Bool) (σ := Nat))
      (loop.compile order) (point (A := word) (0 : Word) 2) = Part.some (point (A := word) (3 : Word) 2777) := by
  rw [loop.step_observe, Part.eq_some_iff, Part.mem_map_iff]
  refine ⟨((3 : Word), 2777), ?_, rfl⟩
  rw [Elgot.StateT.run_iter, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.more (a' := ((1 : Word), 27))
  · rw [step_run]; exact Part.mem_some _
  apply Elgot.Part.Runs.more (a' := ((2 : Word), 277))
  · rw [step_run]; exact Part.mem_some _
  apply Elgot.Part.Runs.done
  rw [step_run]
  exact Part.mem_some _

example (order : Bool) :
    ∃ fuel, ((lower width (recovered order)).run (eval (σ := Nat) codec) fuel (packet codec (0 : Word))).run 2 =
      Part.some (some (packet codec (3 : Word)), 2777) :=
  (returns_iff codec (recovered order) (0 : Word) (3 : Word) 2 2777).mp (source_returns order)

private theorem source_undefined (order : Bool) :
    NestedTheta.Partial.observe (PureGamma.model (Φ := Op) (ε := Bool) (σ := Nat))
      (loop.compile order) (point (A := word) (98 : Word) 2) = Part.none := by
  rw [loop.step_observe, Elgot.StateT.run_iter]
  change Part.map _ (iter step ((98 : Word), 2)) = Part.none
  have restart : iter step ((98 : Word), 2) = iter step ((99 : Word), 27) := by
    rw [congrFun (Elgot.Part.fixpoint step) ((98 : Word), 2)]
    change (Elgot.StateT.body (loop.step (σ := Nat)) ((98 : Word), 2)).bind _ = _
    rw [step_run]
    exact Part.bind_some _ _
  have blocked : iter step ((99 : Word), 27) = Part.none := by
    rw [congrFun (Elgot.Part.fixpoint step) ((99 : Word), 27)]
    change (Elgot.StateT.body (loop.step (σ := Nat)) ((99 : Word), 27)).bind _ = _
    rw [step_run]
    exact Part.bind_none _
  rw [restart, blocked, Part.map_none]

/-- No budget returns any output packet and store after the selected
classifier is undefined. The failed activation is reached after a restart. -/
example (order : Bool) (output : Env [width]) (final : Nat) :
    ¬ ∃ fuel, ((lower width (recovered order)).run (eval (σ := Nat) codec) fuel (packet codec (98 : Word))).run 2 =
      Part.some (some output, final) := by
  cases output with
  | cons y tail =>
    cases tail
    have packed : packet codec (codec.symm y) = .cons y .nil := by
      unfold packet
      rw [Equiv.apply_symm_apply]
    rw [← packed, ← returns_iff codec (recovered order), source_undefined]
    simp

-- Execute the actual ordered CF blocks with the same classifier transition
-- function in an executable state monad. This also checks the entry and
-- exit block costs and both recovered row placements.
private def executable {Γ Δ : List Width} (body : Body Op Bool word width Γ Δ) (env : Env Γ) :
    StateT Nat Option (Env Δ) :=
  body.eval codec (fun _ _ x => (show Word from x) + 1) (fun _ x => StateT.mk (classify x)) env

private def outputPair : Option (Env [width]) × Nat → Option (Word × Nat)
  | (some (.cons x .nil), token) => some (x, token)
  | (none, _) => none

set_option interpreter.prefer_native false in
#eval show IO Unit from do
  for order in [false, true] do
    let some fibre := PureTheta.Reverse.recover (loop.compile order)
      | throw (IO.userError "mixed theta recovery failed")
    unless fibre.pureFirst == order do
      throw (IO.userError "mixed theta recovery lost the binding order")
    let cfg := lower width fibre
    let run fuel (x : Word) := ((cfg.run executable fuel (packet codec x)).run 2)
    unless (run 4 0).bind outputPair == none && (run 5 0).bind outputPair == some (3, 2777) do
      throw (IO.userError "ordered CF lost a feedback or exit store")
    let reachedBlocked := match run 2 98 with | some (none, 27) => true | _ => false
    unless reachedBlocked && (run 5 98).isNone do
      throw (IO.userError "ordered CF lost the store before the undefined classifier or returned after it")

end Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Regression
