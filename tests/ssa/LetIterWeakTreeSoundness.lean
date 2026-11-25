module

import Silmaril.Semantics.ITree.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SingleCall.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms

/-! A mixed weak interaction-tree model and original-bound endpoint reflection
for the open unary source fragment. -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.Semantics.Categorical (denote_eq_of_abortEquiv_nil)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.Semantics
open Silmaril.Elgot

namespace LetIterWeakTreeSoundness

inductive Prim where
  | next
  | unitMap
  | stop (label : Bool)

abbrev T := Ty Unit
abbrev atom : T := .base ()
abbrev Fx := Bool × Bool
abbrev bound : Fx := (true, false)

instance : HasTy Prim T :=
  ⟨fun | .next => atom | _ => unit,
   fun | .next => atom | .unitMap => unit | .stop _ => empty⟩
instance : HasEff Prim Fx := ⟨fun | .stop _ => bound | _ => ⊥⟩
instance : EffectIteration Fx := EffectIteration.complete Fx

def chain : Nat → Expr Prim
  | 0 => .var 0
  | n + 1 => .op .next (chain n)

abbrev Γ₁ : EffectCtx T Fx := [(atom, ⊥)]

theorem chain_typed (n : Nat) (e : Fx) : Wf Γ₁ (chain n) atom e := by
  induction n with
  | zero => exact .var (Γ := Γ₁) 0 bot_le
  | succ n ih => exact .op (f := Prim.next) bot_le ih

inductive Events : Type → Type
  | stop (label : Bool) : Events PEmpty

abbrev D (S : Type 1) := Ty.denote (fun _ : Unit => S)
abbrev free := (Ctx.nil : Ctx Empty T)
abbrev β₁ := Γ₁.toBoundCtx

noncomputable def treeInstr (S : Type 1) (step : S → S) :
    InstructionModel (D S) Prim (ITree.Tree Events) where
  eval
    | .next, x => ITree.ret (step x)
    | .unitMap, x => ITree.ret x
    | .stop b, _ => ITree.vis (.stop b) (fun x => x.elim)

theorem treeInstr_respectsPure (S : Type 1) (step : S → S) :
    InstructionModel.RespectsPure (ε := Fx) (treeInstr S step) := by
  intro f h
  cases f with
  | next => exact ⟨step, fun _ => rfl⟩
  | unitMap => exact ⟨id, fun _ => rfl⟩
  | stop b =>
    have hne : bound ≠ (⊥ : Fx) := by decide
    exact (hne h).elim

def observeHead {A X : Type 1} : ITree.Visible Events A X → Option Bool
  | .ret _ => none
  | .vis (.stop b) _ => some b

noncomputable def headLabel {A : Type 1} (t : ITree.Tree Events A) : _root_.Part (Option Bool) :=
  (ITree.out t).map observeHead

def nativeChain : Nat → Tm Empty Prim 1
  | 0 => .bv 0
  | n + 1 => .op .next (nativeChain n)

theorem chain_lowers (n : Nat) : (chain n).toLetIter 1 = some (nativeChain n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chain, nativeChain, Expr.toLetIter, ih]

def chainDeriv (n : Nat) : Derivation Prim free β₁ (nativeChain n) atom :=
  match n with
  | 0 => .bv (ι := 0)
  | n + 1 => .op (chainDeriv n)

def freeEnv (S : Type 1) : FreeEnv (D S) free := fun x => x.elim

def env₁ (S : Type 1) (x : S) : BoundEnv (D S) β₁ :=
  BoundEnv.snoc (β := .nil) (fun i => i.elim0) x

noncomputable def evalChain (S : Type 1) (step : S → S) (n : Nat) (x : S) :
    ITree.Tree Events S :=
  Derivation.denote (D S) (treeInstr S step) (chainDeriv n) (freeEnv S) (env₁ S x)

def applyN {S : Type 1} (step : S → S) : Nat → S → S
  | 0, x => x
  | n + 1, x => step (applyN step n x)

theorem evalChain_ret (S : Type 1) (step : S → S) (n : Nat) (x : S) :
    evalChain S step n x = ITree.ret (applyN step n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((evalChain S step n x) >>= (fun x => ITree.ret (step x))) =
      ITree.ret (step (applyN step n x))
    rw [ih]
    exact pure_bind _ _

abbrev N := ULift.{1} Nat
def nextNat (n : N) : N := ⟨n.down + 1⟩

theorem evalChain_N (n : Nat) : evalChain N nextNat n ⟨0⟩ = ITree.ret (⟨n⟩ : N) := by
  have h : applyN nextNat n ⟨0⟩ = (⟨n⟩ : N) := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg nextNat ih
  rw [evalChain_ret, h]

/-- The soundness step accepts any derivation, including one with native
iteration or an above-bound subterm in an intermediate expression. -/
theorem native_chain_eq_iff (n m : Nat) :
    AbortEquiv (⊥ : Fx) free β₁ (nativeChain n) (nativeChain m) atom ↔ n = m := by
  constructor
  · intro h
    have he : evalChain N nextNat n ⟨0⟩ = evalChain N nextNat m ⟨0⟩ :=
      denote_eq_of_abortEquiv_nil (fun _ : Unit => N) (treeInstr N nextNat)
        (treeInstr_respectsPure N nextNat) h (chainDeriv n) (chainDeriv m) (env₁ N ⟨0⟩)
    rw [evalChain_N, evalChain_N, ITree.ret_inj] at he
    exact congrArg ULift.down he
  · rintro rfl
    exact .equiv (.refl (chainDeriv n).toHasType)

/-- Endpoint conservativity on unary words at the source's original bound. -/
theorem unary_endpoint_conservativity (e : Fx) (n m : Nat) :
    AbortEquiv (⊥ : Fx) free β₁ (nativeChain n) (nativeChain m) atom ↔
      Eqv Γ₁ atom e (chain n) (chain m) := by
  constructor
  · intro h
    obtain rfl := (native_chain_eq_iff n m).mp h
    exact .refl (chain_typed n e)
  · intro h
    exact h.toLetIter (chain_lowers n) (chain_lowers m)

def unitProg : Expr Prim := .op .unitMap .unit
def unitDeriv : Derivation Prim free .nil (.unit : Tm Empty Prim 0) unit := .unit
def unitProgDeriv : Derivation Prim free .nil (.op .unitMap .unit : Tm Empty Prim 0) unit :=
  .op .unit

theorem terminality_without_events (S : Type 1) (step : S → S) :
    Eqv ([] : EffectCtx T Fx) unit (⊥ : Fx) unitProg .unit ∧
    Derivation.denoteClosed (D S) (treeInstr S step) unitProgDeriv =
      Derivation.denoteClosed (D S) (treeInstr S step) unitDeriv := by
  refine ⟨.step (.terminal (.op le_rfl (.unit _ _)) (.unit _ _)), ?_⟩
  simp only [Derivation.denoteClosed, unitProgDeriv, unitDeriv, Derivation.denote]
  erw [pure_bind]
  rfl

def abortLeft (b : Bool) : Expr Prim := .let₁ (.abort (.op (.stop b) .unit)) unitProg
def abortRight (b : Bool) : Expr Prim :=
  .let₁ (.op (.stop b) .unit) (.let₁ (.abort (.var 0)) unitProg)
def leftNative (b : Bool) : Tm Empty Prim 0 :=
  .let₁ (.abort (.op (.stop b) .unit)) (.op .unitMap .unit)
def rightNative (b : Bool) : Tm Empty Prim 0 :=
  .let₁ (.op (.stop b) .unit) (.let₁ (.abort (.bv 0)) (.op .unitMap .unit))

def leftTyped (b : Bool) : TypedExpr Prim ([] : EffectCtx T Fx) unit bound :=
  ⟨abortLeft b, .let₁ (A := unit) (.abort (.op le_rfl (.unit _ _))) (.op bot_le (.unit _ _))⟩
def rightTyped (b : Bool) : TypedExpr Prim ([] : EffectCtx T Fx) unit bound :=
  ⟨abortRight b, .let₁ (.op le_rfl (.unit _ _))
    (.let₁ (A := unit) (.abort (.var 0 bot_le)) (.op bot_le (.unit _ _)))⟩
def leftDeriv (b : Bool) : Derivation Prim free .nil (leftNative b) unit :=
  .let₁ (A := unit) (.abort (.op .unit)) (.op .unit)
def rightDeriv (b : Bool) : Derivation Prim free .nil (rightNative b) unit :=
  .let₁ (.op .unit) (.let₁ (A := unit) (.abort (.bv (ι := 0))) (.op .unit))

theorem observe_stop_bind (S : Type 1) (b : Bool)
    (k : D S empty → ITree.Tree Events (D S unit)) :
    headLabel (ITree.vis (.stop b) (fun x : PEmpty => x.elim) >>= k) =
      .some (some b) := by
  rw [ITree.vis_bind]
  simp [headLabel, observeHead]

theorem strict_bound_abort (S : Type 1) (step : S → S) (b : Bool) :
    (⊥ : Fx) < bound ∧ bound < ⊤ ∧
    Eqv ([] : EffectCtx T Fx) unit bound (abortLeft b) (abortRight b) ∧
    HasTypeEffect free .nil (leftNative b) unit bound ∧
    HasTypeEffect free .nil (rightNative b) unit bound ∧
    Derivation.denoteClosed (D S) (treeInstr S step) (leftDeriv b) =
      Derivation.denoteClosed (D S) (treeInstr S step) (rightDeriv b) ∧
    headLabel (Derivation.denoteClosed (D S) (treeInstr S step) (rightDeriv b)) =
      .some (some b) := by
  have h : Eqv ([] : EffectCtx T Fx) unit bound (abortLeft b) (abortRight b) :=
    .step (.rewrite (leftTyped b).prop (rightTyped b).prop (.let1_abort _ _))
  obtain ⟨ht, hs, he⟩ := Eqv.toLetIter_at_bound (leftTyped b) (rightTyped b) h rfl rfl
  refine ⟨lt_of_le_of_ne bot_le (by decide), lt_of_le_of_ne le_top (by decide), h, ht, hs, ?_, ?_⟩
  · exact denote_eq_of_abortEquiv_nil (fun _ : Unit => S) (treeInstr S step)
      (treeInstr_respectsPure S step) he (leftDeriv b) (rightDeriv b) (fun i => i.elim0)
  · change headLabel (((pure (PUnit.unit : D S unit) : ITree.Tree Events _) >>=
      (fun _ => ITree.vis (.stop b) (fun x : PEmpty => x.elim : PEmpty → ITree.Tree Events (D S empty))))
      >>= _) = _
    rw [pure_bind]
    exact observe_stop_bind S b _

end LetIterWeakTreeSoundness

namespace LetIterResponseSingleCall

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

inductive Prim where
  | next
  | read

abbrev Fx := Bool × Bool
abbrev strict : Fx := (true, false)
abbrev T := Ty Bool
abbrev inputSort : T := .base false
abbrev outputSort : T := .base true

/-- Both calls have one argument. The read returns a different sort. -/
abbrev sig : Signature Bool Prim :=
  ⟨fun _ => 1, fun _ _ => false, fun | .next => false | .read => true⟩

local instance : HasTy Prim T := sig.endpoints
local instance : HasEff Prim Fx := ⟨fun | .next => ⊥ | .read => strict⟩
local instance : EffectIteration Fx := EffectIteration.complete Fx

abbrev Γ : EffectCtx T Fx := [(outputSort, ⊥), (inputSort, ⊥)]
abbrev sorts : Fin Γ.length → Bool := Fin.cases true (fun _ => false)
abbrev Γ' : EffectCtx T Fx := (outputSort, ⊥) :: Γ
abbrev sorts' : Fin Γ'.length → Bool := Fin.cases true sorts
abbrev Γ₀ := (Ctx.nil : Ctx Empty T)

theorem ctx_pure : Γ.Pure := by
  unfold EffectCtx.Pure
  decide

theorem slots_typed : ∀ i : Fin Γ.length, (Γ.get i).1 = .base (sorts i) := by
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  rw [Fin.eq_zero j]
  rfl

theorem extended_slots_typed : ∀ i : Fin Γ'.length, (Γ'.get i).1 = .base (sorts' i) :=
  fun i => Fin.cases (motive := fun j => (Γ'.get j).1 = .base (sorts' j)) rfl slots_typed i

abbrev args : (i : Fin (sig.arity Prim.read)) → Tree sig sorts (sig.arg Prim.read i) :=
  fun _ => .op Prim.next (fun _ => .var 1)

theorem args_pure : ∀ i, DeclaredPure (ε := Fx) sig (args i) :=
  fun _ => ⟨rfl, fun _ => trivial⟩

theorem read_not_pure : ¬ IsPure (⊥ : Fx) Prim.read := by
  change strict ≠ (⊥ : Fx)
  decide

theorem strict_bound : (⊥ : Fx) < strict ∧ strict < ⊤ :=
  ⟨lt_of_le_of_ne bot_le (by decide), lt_of_le_of_ne le_top (by decide)⟩

abbrev request : Tree sig sorts true := .op Prim.read args
abbrev receive : Expr Prim := .var 0
abbrev ignoreResponse : Expr Prim := .var 1
abbrev receiveThroughLet : Expr Prim := .let₁ (.var 0) (.var 0)

theorem receive_wf : Wf Γ' receive outputSort (⊥ : Fx) := .var 0 le_rfl
theorem ignore_wf : Wf Γ' ignoreResponse outputSort (⊥ : Fx) := .var 1 le_rfl
theorem receive_let_wf : Wf Γ' receiveThroughLet outputSort (⊥ : Fx) :=
  .let₁ receive_wf (.var 0 le_rfl)

/-- The same normalized request distinguishes returning its response from
returning the existing variable of the same result sort. -/
theorem response_differs_from_ambient :
    ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx (.let₁ request.native (.bv 0))
      (.let₁ request.native (.bv 1)) outputSort := by
  intro h
  have he := Response.SingleCall.continuation_eqv sig ctx_pure slots_typed args args_pure
    read_not_pure strict le_rfl receive_wf ignore_wf (t := .bv 0) (s := .bv 1) rfl rfl h
  let x : Tree sig sorts' true := .var 0
  let y : Tree sig sorts' true := .var 1
  have hΓ' : Γ'.Pure := by unfold EffectCtx.Pure; decide
  have eqTrees := (source_eqv_iff sig x y trivial trivial hΓ' extended_slots_typed strict).mp he
  let index {a : Bool} (z : Tree sig sorts' a) : Option Nat := match z with
    | .var i => some i.val
    | .op _ _ => none
  exact (by decide : (some 0 : Option Nat) ≠ some 1) (congrArg index eqTrees)

theorem response_differs_from_ambient_at_bound :
    ¬ Eqv Γ outputSort strict (.let₁ request.source receive)
      (.let₁ request.source ignoreResponse) := by
  intro h
  exact response_differs_from_ambient (h.toLetIter rfl rfl)

/-- A let in the continuation is normalized automatically at the original bound. -/
theorem let_in_continuation :
    AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx (.let₁ request.native (.let₁ (.bv 0) (.bv 0)))
      (.let₁ request.native (.bv 0)) outputSort ↔
    Eqv Γ outputSort strict (.let₁ request.source receiveThroughLet)
      (.let₁ request.source receive) :=
  Response.SingleCall.endpoint_reflection sig ctx_pure slots_typed args args_pure
    read_not_pure strict le_rfl receive_let_wf receive_wf rfl rfl

example : Eqv Γ outputSort strict (.let₁ request.source receiveThroughLet)
    (.let₁ request.source receive) := by
  have ht : Wf Γ request.source outputSort strict :=
    .op (f := Prim.read) le_rfl
      (.pair (.op (f := Prim.next) bot_le (.pair (.var 1 bot_le) (.unit _ _))) (.unit _ _))
  obtain ⟨t, hl, htyped⟩ := ht.toLetIter
  have he : t = request.native := Option.some.inj (hl.symm.trans rfl)
  subst t
  exact let_in_continuation.mp (.equiv (.let₁ (.refl htyped.1) (Equiv.letEta .bv)))

end LetIterResponseSingleCall
