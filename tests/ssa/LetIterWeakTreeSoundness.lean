module

import Silmaril.Semantics.ITree.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree.Reorder.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.RawArms.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Compile.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Cyclic.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Structured.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Context.Thms
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
  | readOther
  | readAlt
  | join

abbrev Fx := Bool × Bool
abbrev strict : Fx := (true, false)
abbrev T := Ty Bool
abbrev inputSort : T := .base false
abbrev outputSort : T := .base true

/-- The reads include two operations at the same type and one at the opposite
type. The pure join takes two ordered arguments. -/
abbrev sig : Signature Bool Prim :=
  ⟨fun | .join => 2 | _ => 1,
    fun f _ => match f with | .readOther | .join => true | _ => false,
    fun | .read | .readAlt | .join => true | _ => false⟩

local instance : HasTy Prim T := sig.endpoints
local instance : HasEff Prim Fx := ⟨fun | .next | .join => ⊥ | _ => strict⟩
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

theorem read_other_not_pure : ¬ IsPure (⊥ : Fx) Prim.readOther := by
  change strict ≠ (⊥ : Fx)
  decide

abbrev otherArgs : Response.Args sig sorts Prim.readOther := fun _ => .var 0

/-- The request equality resolves the primitive before comparing its dependent
argument tuple, even when the response sorts differ. -/
example : ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx (.let₁ request.native (.bv 0))
    (.let₁ (Tree.op Prim.readOther otherArgs).native (.bv 1)) outputSort := by
  intro hn
  have h := Response.SingleCall.request_eq sig slots_typed args otherArgs
    args_pure (fun _ => trivial) read_not_pure read_other_not_pure hn
  have hfg : Prim.read = Prim.readOther := congrArg Sigma.fst h
  cases hfg

abbrev normArg : Expr Prim := sourceTuple 1 (fun i => (args i).source)
abbrev normArgNative : Tm Empty Prim Γ.length := nativeTuple 1 (fun i => (args i).native)
abbrev rawArg : Expr Prim := .let₁ normArg (.var 0)
abbrev rawArgNative : Tm Empty Prim Γ.length := .let₁ normArgNative (.bv 0)

theorem arg_wf : Wf Γ normArg (input (sig.arity Prim.read) (sig.arg Prim.read)) (⊥ : Fx) :=
  .pair (.op (f := Prim.next) le_rfl (.pair (.var 1 le_rfl) (.unit _ _))) (.unit _ _)

example : Eqv Γ outputSort strict (.let₁ (.op Prim.read rawArg) receive)
    (.let₁ (.op Prim.read normArg) receive) := by
  have hreflect := Response.SingleCall.endpoint_reflection_pure_arguments sig ctx_pure slots_typed
    read_not_pure read_not_pure strict le_rfl le_rfl
    (x := rawArg) (y := normArg) (.let₁ arg_wf (.var 0 le_rfl)) arg_wf receive_wf receive_wf
    (x₀ := rawArgNative) (y₀ := normArgNative) (t := .bv 0) (s := .bv 0) rfl rfl rfl rfl
  obtain ⟨arg, hl, ht⟩ := arg_wf.toLetIter
  have he : arg = normArgNative := Option.some.inj (hl.symm.trans rfl)
  subst arg
  exact hreflect.mp (.equiv (.let₁ (.op (Equiv.letEta ht.1)) (.refl .bv)))

abbrev useFirstResponse : Response.Sequence sig true sorts :=
  .call Prim.read args (.call Prim.readOther (fun _ => .var 0) (.ret (.var 1)))

abbrev useAmbientAtSecondCall : Response.Sequence sig true sorts :=
  .call Prim.read args (.call Prim.readOther (fun _ => .var 1) (.ret (.var 1)))

abbrev returnAmbientAfterTwoCalls : Response.Sequence sig true sorts :=
  .call Prim.read args (.call Prim.readOther (fun _ => .var 0) (.ret (.var 2)))

theorem firstResponse_wf : Response.Sequence.WellTyped sig strict useFirstResponse :=
  ⟨args_pure, read_not_pure, le_rfl, fun _ => trivial, read_other_not_pure, le_rfl, trivial⟩

theorem ambientAtSecondCall_wf : Response.Sequence.WellTyped sig strict useAmbientAtSecondCall :=
  ⟨args_pure, read_not_pure, le_rfl, fun _ => trivial, read_other_not_pure, le_rfl, trivial⟩

theorem ambientAfterTwoCalls_wf : Response.Sequence.WellTyped sig strict returnAmbientAfterTwoCalls :=
  ⟨args_pure, read_not_pure, le_rfl, fun _ => trivial, read_other_not_pure, le_rfl, trivial⟩

/-- The first response and a same-sort ambient variable give distinguishable
requests at the second call. -/
example : ¬ Eqv Γ outputSort strict useFirstResponse.source useAmbientAtSecondCall.source := by
  intro h
  have hn := (Response.Sequence.endpoint_reflection sig ctx_pure slots_typed strict
    useFirstResponse useAmbientAtSecondCall firstResponse_wf ambientAtSecondCall_wf).mpr h
  have he := Response.Sequence.native_eq_implies_eq sig slots_typed strict
    useFirstResponse useAmbientAtSecondCall firstResponse_wf ambientAtSecondCall_wf hn
  let secondArgument : Expr Prim → Option Nat
    | .let₁ _ (.let₁ (.op _ (.pair (.var i) .unit)) _) => some i
    | _ => none
  have hi := congrArg (fun p => secondArgument (Response.Sequence.source sig p)) he
  exact (by decide : (some 0 : Option Nat) ≠ some 1) hi

/-- After the second call, the first response is at index one and the
original same-sort ambient variable is at index two. -/
example : ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx
    useFirstResponse.native returnAmbientAfterTwoCalls.native outputSort := by
  intro hn
  have he := Response.Sequence.native_eq_implies_eq sig slots_typed strict
    useFirstResponse returnAmbientAfterTwoCalls firstResponse_wf ambientAfterTwoCalls_wf hn
  let finalVariable : Expr Prim → Option Nat
    | .let₁ _ (.let₁ _ (.var i)) => some i
    | _ => none
  have hi := congrArg (fun p => finalVariable (Response.Sequence.source sig p)) he
  exact (by decide : (some 1 : Option Nat) ≠ some 2) hi

example : useFirstResponse.source.toLetIter Γ.length =
    some (.let₁ request.native (.let₁ (.op Prim.readOther (.pair (.bv 0) .unit)) (.bv 1))) :=
  Response.Sequence.lowers sig useFirstResponse

abbrev returnAfterFirstCall : Response.Sequence sig true sorts :=
  .call Prim.read args (.ret (.var 0))

/-- A pure return is observable where the longer sequence makes its second call. -/
example : ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx
    returnAfterFirstCall.native useFirstResponse.native outputSort := by
  intro hn
  have hshort : Response.Sequence.WellTyped sig strict returnAfterFirstCall :=
    ⟨args_pure, read_not_pure, le_rfl, trivial⟩
  have he := Response.Sequence.native_eq_implies_eq sig slots_typed strict
    returnAfterFirstCall useFirstResponse hshort firstResponse_wf hn
  let continuationCalls : Expr Prim → Bool
    | .let₁ _ (.let₁ _ _) => true
    | _ => false
  have h := congrArg (fun p => continuationCalls (Response.Sequence.source sig p)) he
  exact (by decide : false ≠ true) h

open Response.Flatten

abbrev pureOperand : Tree sig sorts false := .op Prim.next (fun _ => .var 1)
abbrev rawLeft : Program sig sorts true :=
  .let1 (.tree pureOperand) (.unary Prim.read rfl (.tree (.var 0)))
abbrev rawRight : Program sig sorts true :=
  .unary Prim.readAlt rfl (.tree (.var 1))

abbrev leftFirst : Program sig sorts true :=
  .binary Prim.join rfl rawLeft rawRight
abbrev rightFirst : Program sig sorts true :=
  .binary Prim.join rfl rawRight rawLeft

theorem typedLeft : Program.WellTyped sig strict rawLeft :=
  ⟨⟨rfl, fun _ => trivial⟩, le_rfl, trivial⟩

theorem typedRight : Program.WellTyped sig strict rawRight := ⟨le_rfl, trivial⟩

theorem typedLeftFirst : Program.WellTyped sig strict leftFirst :=
  ⟨bot_le, typedLeft, typedRight⟩
theorem typedRightFirst : Program.WellTyped sig strict rightFirst :=
  ⟨bot_le, typedRight, typedLeft⟩

noncomputable abbrev leftCode := compile (ε := Fx) sig leftFirst
noncomputable abbrev rightCode := compile (ε := Fx) sig rightFirst

def firstInstruction (p : Response.Sequence sig true sorts) : Option Prim :=
  match p with
  | .ret _ => none
  | .call f _ _ => some f

theorem read_alt_not_pure : ¬ IsPure (⊥ : Fx) Prim.readAlt := by
  change strict ≠ (⊥ : Fx)
  decide

theorem leftHead : firstInstruction leftCode = some Prim.read := by
  simp only [leftCode, compile, unaryTail, emit,
    ite_eq_right read_not_pure, Response.Sequence.bind, Response.Sequence.subst, firstInstruction]

theorem rightHead : firstInstruction rightCode = some Prim.readAlt := by
  simp only [rightCode, compile, unaryTail, emit,
    ite_eq_right read_alt_not_pure, Response.Sequence.bind, Response.Sequence.subst, firstInstruction]

def visibleOrder : {n : Nat} → {ts : Fin n → Bool} → {c : Bool} →
    Response.Sequence sig c ts → List Prim
  | _, _, _, .ret _ => []
  | _, _, _, .call f _ rest => f :: visibleOrder rest

theorem join_pure : IsPure (⊥ : Fx) Prim.join := rfl

example : visibleOrder leftCode = [Prim.read, Prim.readAlt] := by
  simp only [leftCode, compile, unaryTail, binaryTail, emit,
    ite_eq_right read_not_pure, ite_eq_right read_alt_not_pure, ite_eq_left join_pure,
    Response.Sequence.bind, Response.Sequence.weaken, Response.Sequence.subst, visibleOrder]

/-- An effectful unary argument finishes its own call before the outer call. -/
example : visibleOrder (compile (ε := Fx) sig (.unary Prim.readOther rfl rawLeft)) =
    [Prim.read, Prim.readOther] := by
  simp only [compile, unaryTail, emit, ite_eq_right read_not_pure,
    ite_eq_right read_other_not_pure, Response.Sequence.bind, Response.Sequence.subst, visibleOrder]

/-- Swapping the effectful operands changes the head even though the final
binary primitive is pure. The left operand starts with a pure let. -/
theorem swapped_arguments_source_ne :
    ¬ Eqv Γ outputSort strict leftFirst.source rightFirst.source := by
  intro h
  have hl := compile_eqv sig ctx_pure slots_typed strict leftFirst typedLeftFirst
  have hr := compile_eqv sig ctx_pure slots_typed strict rightFirst typedRightFirst
  have hseq := hl.symm.trans (h.trans hr)
  have hn := hseq.toLetIter (Response.Sequence.lowers sig leftCode) (Response.Sequence.lowers sig rightCode)
  have he := Response.Sequence.native_eq_implies_eq sig slots_typed strict leftCode rightCode
    (compile_typed sig strict leftFirst typedLeftFirst)
    (compile_typed sig strict rightFirst typedRightFirst) hn
  have hhead := leftHead.symm.trans ((congrArg firstInstruction he).trans rightHead)
  cases hhead

/-- The lowered raw programs are separated even when the native proof can use
all well-typed intermediate terms. -/
theorem swapped_arguments_native_ne {t s : Tm Empty Prim Γ.length}
    (ht : leftFirst.source.toLetIter Γ.length = some t)
    (hs : rightFirst.source.toLetIter Γ.length = some s) :
    ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx t s outputSort := by
  intro hn
  exact swapped_arguments_source_ne
    ((endpoint_reflection sig ctx_pure slots_typed strict leftFirst rightFirst
      typedLeftFirst typedRightFirst ht hs).mp hn)

example : ∃ t s : Tm Empty Prim Γ.length,
    leftFirst.source.toLetIter Γ.length = some t ∧
    rightFirst.source.toLetIter Γ.length = some s ∧
    ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx t s outputSort := by
  obtain ⟨t, ht, _⟩ := (source_wf sig ctx_pure slots_typed strict leftFirst typedLeftFirst).toLetIter
  obtain ⟨s, hs, _⟩ := (source_wf sig ctx_pure slots_typed strict rightFirst typedRightFirst).toLetIter
  exact ⟨t, s, ht, hs, swapped_arguments_native_ne ht hs⟩

section EffectfulCase

abbrev Γsum : EffectCtx T Fx := (Ty.coprod inputSort outputSort, ⊥) :: Γ
abbrev Γleft : EffectCtx T Fx := (inputSort, ⊥) :: Γ
abbrev Γright : EffectCtx T Fx := (outputSort, ⊥) :: Γ
abbrev leftSlots : Fin Γleft.length → Bool := Response.extendSorts false sorts
abbrev rightSlots : Fin Γright.length → Bool := Response.extendSorts true sorts

abbrev leftArm : Program sig leftSlots true :=
  .unary Prim.read rfl (.tree (.var 0))
abbrev changedLeft : Program sig leftSlots true :=
  .unary Prim.readAlt rfl (.tree (.var 0))

/-- The right arm uses its own payload to issue a request at a different type.
Its response becomes the argument of the next request. -/
abbrev rightArm : Program sig rightSlots true :=
  .let1 (.unary Prim.readOther rfl (.tree (.var 0)))
    (.unary Prim.readAlt rfl (.tree (.var 0)))
abbrev changedRight : Program sig rightSlots true :=
  .unary Prim.readAlt rfl (.tree (.var 2))

private theorem leftArm_typed : Program.WellTyped sig strict leftArm := ⟨le_rfl, trivial⟩
private theorem changedLeft_typed : Program.WellTyped sig strict changedLeft := ⟨le_rfl, trivial⟩
private theorem rightArm_typed : Program.WellTyped sig strict rightArm :=
  ⟨⟨le_rfl, trivial⟩, le_rfl, trivial⟩
private theorem changedRight_typed : Program.WellTyped sig strict changedRight := ⟨le_rfl, trivial⟩

private theorem branchSlots {a : Bool} :
    ∀ i : Fin ((Ty.base a, (⊥ : Fx)) :: Γ).length,
      (((Ty.base a, (⊥ : Fx)) :: Γ).get i).1 = .base (Response.extendSorts a sorts i) :=
  fun i => Fin.cases (motive := fun j =>
    (((Ty.base a, (⊥ : Fx)) :: Γ).get j).1 = .base (Response.extendSorts a sorts j))
    rfl slots_typed i

private theorem branchPure (a : Bool) : EffectCtx.Pure ((Ty.base a, (⊥ : Fx)) :: Γ) :=
  fun i => Fin.cases (motive := fun j => (((Ty.base a, (⊥ : Fx)) :: Γ).get j).2 = ⊥)
    rfl ctx_pure i

private theorem caseWf (l : Program sig leftSlots true) (r : Program sig rightSlots true)
    (hl : Program.WellTyped sig strict l) (hr : Program.WellTyped sig strict r) :
    Wf Γsum (Response.Case.onHead l.source r.source) outputSort strict :=
  Response.Case.source_wf
    (source_wf sig (branchPure false) branchSlots strict l hl)
    (source_wf sig (branchPure true) branchSlots strict r hr)

private theorem unequalOrders {Δ : EffectCtx T Fx} {ss : Fin Δ.length → Bool}
    (hΔ : Δ.Pure) (hs : ∀ i, (Δ.get i).1 = .base (ss i))
    (p q : Program sig ss true) (hp : Program.WellTyped sig strict p)
    (hq : Program.WellTyped sig strict q)
    (h : visibleOrder (compile (ε := Fx) sig p) ≠ visibleOrder (compile (ε := Fx) sig q)) :
    ¬ Eqv Δ outputSort strict p.source q.source := by
  intro he
  have ep := compile_eqv sig hΔ hs strict p hp
  have eq := compile_eqv sig hΔ hs strict q hq
  have hn := (ep.symm.trans (he.trans eq)).toLetIter
    (Response.Sequence.lowers sig (compile (ε := Fx) sig p))
    (Response.Sequence.lowers sig (compile (ε := Fx) sig q))
  exact h (congrArg visibleOrder (Response.Sequence.native_eq_implies_eq sig hs strict _ _
    (compile_typed sig strict p hp) (compile_typed sig strict q hq) hn))

private theorem leftOrder :
    visibleOrder (compile (ε := Fx) sig leftArm) = [Prim.read] := by
  simp only [compile, unaryTail, emit, ite_eq_right read_not_pure, Response.Sequence.bind,
    Response.Sequence.subst, visibleOrder]

private theorem changedLeftOrder :
    visibleOrder (compile (ε := Fx) sig changedLeft) = [Prim.readAlt] := by
  simp only [compile, unaryTail, emit, ite_eq_right read_alt_not_pure, Response.Sequence.bind,
    Response.Sequence.subst, visibleOrder]

private theorem rightOrder :
    visibleOrder (compile (ε := Fx) sig rightArm) = [Prim.readOther, Prim.readAlt] := by
  simp only [compile, unaryTail, emit, ite_eq_right read_other_not_pure,
    ite_eq_right read_alt_not_pure, Response.Sequence.bind, Response.Sequence.subst, visibleOrder]

private theorem changedRightOrder :
    visibleOrder (compile (ε := Fx) sig changedRight) = [Prim.readAlt] := by
  simp only [compile, unaryTail, emit, ite_eq_right read_alt_not_pure, Response.Sequence.bind,
    Response.Sequence.subst, visibleOrder]

/-- Changing either arm is visible, even though the other arm and scrutinee are
identical. The three raw cases lower at the original strict bound. -/
theorem effectful_case_observes_both_tags :
    ∃ t l r : Tm Empty Prim Γsum.length,
      (Response.Case.onHead leftArm.source rightArm.source).toLetIter Γsum.length = some t ∧
      (Response.Case.onHead changedLeft.source rightArm.source).toLetIter Γsum.length = some l ∧
      (Response.Case.onHead leftArm.source changedRight.source).toLetIter Γsum.length = some r ∧
      ¬ AbortEquiv (⊥ : Fx) Γ₀ Γsum.toBoundCtx t l outputSort ∧
      ¬ AbortEquiv (⊥ : Fx) Γ₀ Γsum.toBoundCtx t r outputSort := by
  obtain ⟨t, ht, _⟩ := (caseWf leftArm rightArm leftArm_typed rightArm_typed).toLetIter
  obtain ⟨l, hl, _⟩ := (caseWf changedLeft rightArm changedLeft_typed rightArm_typed).toLetIter
  obtain ⟨r, hr, _⟩ := (caseWf leftArm changedRight leftArm_typed changedRight_typed).toLetIter
  refine ⟨t, l, r, ht, hl, hr, ?_, ?_⟩
  · intro hn
    have he := Response.Case.arms_eqv_of_native sig ctx_pure slots_typed strict
      leftArm changedLeft rightArm rightArm
      leftArm_typed changedLeft_typed rightArm_typed rightArm_typed ht hl hn
    exact unequalOrders (branchPure false) branchSlots leftArm changedLeft leftArm_typed
      changedLeft_typed (by rw [leftOrder, changedLeftOrder]; intro h; cases h) he.1
  · intro hn
    have he := (Response.Case.endpoint_reflection sig ctx_pure slots_typed strict
      leftArm leftArm rightArm changedRight leftArm_typed leftArm_typed
      rightArm_typed changedRight_typed ht hr).mp hn
    have harms := (Response.Case.eqv_iff_arms
      (source_wf sig (branchPure false) branchSlots strict leftArm leftArm_typed)
      (source_wf sig (branchPure true) branchSlots strict rightArm rightArm_typed)
      (source_wf sig (branchPure false) branchSlots strict leftArm leftArm_typed)
      (source_wf sig (branchPure true) branchSlots strict changedRight changedRight_typed)).mp he
    exact unequalOrders (branchPure true) branchSlots rightArm changedRight rightArm_typed
      changedRight_typed (by rw [rightOrder, changedRightOrder]; intro h; cases h) harms.2

end EffectfulCase

section EffectfulDecisionTree

open Response.DecisionTree (Shape)

abbrev Γdec : EffectCtx T Fx :=
  [(Ty.coprod inputSort outputSort, ⊥), (outputSort, ⊥), (Ty.coprod inputSort inputSort, ⊥)]
abbrev firstSplit : Fin Γdec.length := 0
abbrev Γfirst (x : Bool) := SumSplit.branchCtx Γdec firstSplit (.base x)
abbrev secondSplit (x : Bool) : Fin (Γfirst x).length := ⟨2, by change 2 < 3; decide⟩
abbrev Γleaf (x : Bool) := SumSplit.branchCtx (Γfirst x) (secondSplit x) inputSort

abbrev decisionSlots (x : Bool) : Fin (Γleaf x).length → Bool :=
  fun i => if i.val = 0 then x else if i.val = 1 then true else false

private theorem leafSlots_typed (x : Bool) :
    ∀ i : Fin (Γleaf x).length, ((Γleaf x).get i).1 = .base (decisionSlots x i) := by
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  rw [Fin.eq_zero k]
  rfl

abbrev finalShape (x : Bool) : Shape (Γleaf x) :=
  .leaf (decisionSlots x) (leafSlots_typed x)
abbrev laterShape (x : Bool) : Shape (Γfirst x) :=
  .split (secondSplit x) (x := false) (y := false) rfl (finalShape x) (finalShape x)
abbrev fullShape : Shape Γdec :=
  .split firstSplit (x := false) (y := true) rfl (laterShape false) (laterShape true)

abbrev probeEarlier : Response.Flatten.Program sig (decisionSlots false) true :=
  .request Prim.read (fun _ => Tree.var (S := sig) (sorts := decisionSlots false)
    ⟨0, by change 0 < 3; decide⟩)
abbrev probeLater (x : Bool) : Response.Flatten.Program sig (decisionSlots x) true :=
  .request Prim.read (fun _ => Tree.var (S := sig) (sorts := decisionSlots x)
    ⟨2, by change 2 < 3; decide⟩)
abbrev leftTree (p : Response.Flatten.Program sig (decisionSlots false) true) :
    Response.DecisionTree.Program sig true (laterShape false) :=
  .split (secondSplit false) (.leaf p) (.leaf (probeLater false))
abbrev rightTree : Response.DecisionTree.Program sig true (laterShape true) :=
  .split (secondSplit true) (.leaf (probeLater true)) (.leaf (probeLater true))
abbrev decision (p : Response.Flatten.Program sig (decisionSlots false) true) :
    Response.DecisionTree.Program sig true fullShape :=
  .split firstSplit (leftTree p) rightTree

private theorem pureDecisionCtx : Γdec.Pure := by unfold EffectCtx.Pure; decide
private theorem earlier_typed : Response.Flatten.Program.WellTyped sig strict probeEarlier :=
  ⟨le_rfl, fun _ => trivial⟩
private theorem later_typed (x : Bool) : Response.Flatten.Program.WellTyped sig strict (probeLater x) :=
  ⟨le_rfl, fun _ => trivial⟩
private theorem leftTree_typed (p : Response.Flatten.Program sig (decisionSlots false) true)
    (hp : Response.Flatten.Program.WellTyped sig strict p) :
    Response.DecisionTree.Program.WellTyped sig strict (leftTree p) :=
  ⟨hp, later_typed false⟩
private theorem rightTree_typed : Response.DecisionTree.Program.WellTyped sig strict rightTree :=
  ⟨later_typed true, later_typed true⟩
private theorem decision_typed (p : Response.Flatten.Program sig (decisionSlots false) true)
    (hp : Response.Flatten.Program.WellTyped sig strict p) :
    Response.DecisionTree.Program.WellTyped sig strict (decision p) :=
  ⟨leftTree_typed p hp, rightTree_typed⟩

private def nestedRequestIndex : Expr Prim → Option Nat
  | .case (.var 0) (.case (.var 3) (.op .read (.pair (.var i) .unit)) _) _ => some i
  | _ => none

-- At the second test, the first payload is the older of the two binders.
example : nestedRequestIndex (decision probeEarlier).source = some 1 := rfl
example : nestedRequestIndex (decision (probeLater false)).source = some 0 := rfl

private theorem leafRequestsDiffer :
    ¬ Eqv (Γleaf false) outputSort strict probeEarlier.source (probeLater false).source := by
  intro he
  have hpure : (Γleaf false).Pure := by unfold EffectCtx.Pure; decide
  let p := compile (ε := Fx) sig probeEarlier
  let q := compile (ε := Fx) sig (probeLater false)
  have ep := compile_eqv sig hpure (leafSlots_typed false) strict probeEarlier earlier_typed
  have eq := compile_eqv sig hpure (leafSlots_typed false) strict (probeLater false) (later_typed false)
  have hn := (ep.symm.trans (he.trans eq)).toLetIter
    (Response.Sequence.lowers sig p) (Response.Sequence.lowers sig q)
  have h := Response.Sequence.native_eq_implies_eq sig (leafSlots_typed false) strict p q
    (compile_typed sig strict probeEarlier earlier_typed)
    (compile_typed sig strict (probeLater false) (later_typed false)) hn
  let argumentIndex : Expr Prim → Option Nat
    | .let₁ (.op .read (.pair (.var i) .unit)) _ => some i
    | _ => none
  have h0 : argumentIndex p.source = some 0 := by
    simp only [p, compile, emit, ite_eq_right read_not_pure, Response.Sequence.source,
      Tree.source, sourceTuple, argumentIndex]
  have h2 : argumentIndex q.source = some 2 := by
    simp only [q, compile, emit, ite_eq_right read_not_pure, Response.Sequence.source,
      Tree.source, sourceTuple, argumentIndex]
  exact (by decide : (some 0 : Option Nat) ≠ some 2)
    (h0.symm.trans ((congrArg (fun p => argumentIndex (Response.Sequence.source sig p)) h).trans h2))

private theorem decisionSourceDiffers :
    ¬ Eqv Γdec outputSort strict (decision probeEarlier).source
      (decision (probeLater false)).source := by
  intro h
  have hL : (Γfirst false).Pure := SumSplit.branchCtx_pure pureDecisionCtx firstSplit inputSort
  have hR : (Γfirst true).Pure := SumSplit.branchCtx_pure pureDecisionCtx firstSplit outputSort
  have hr := Response.DecisionTree.source_wf sig hR strict rightTree rightTree_typed
  have hl := Response.DecisionTree.source_wf sig hL strict (leftTree probeEarlier)
    (leftTree_typed probeEarlier earlier_typed)
  have hl' := Response.DecisionTree.source_wf sig hL strict (leftTree (probeLater false))
    (leftTree_typed (probeLater false) (later_typed false))
  have hleft := (SumSplit.caseArms_eqv_iff firstSplit rfl rfl hl hr hl' hr).mp h
  have hpure : (Γleaf false).Pure :=
    SumSplit.branchCtx_pure hL (secondSplit false) inputSort
  have he := source_wf sig hpure (leafSlots_typed false) strict probeEarlier earlier_typed
  have ha := source_wf sig hpure (leafSlots_typed false) strict (probeLater false) (later_typed false)
  exact leafRequestsDiffer ((SumSplit.caseArms_eqv_iff (secondSplit false) rfl rfl he ha ha ha).mp
    hleft.1).1

/-- The same nested request uses either the earlier payload or the second
payload. A native equality cannot identify those inputs. -/
theorem nested_case_distinguishes_payloads :
    ∃ t s : Tm Empty Prim Γdec.length,
      (decision probeEarlier).source.toLetIter Γdec.length = some t ∧
      (decision (probeLater false)).source.toLetIter Γdec.length = some s ∧
      ¬ AbortEquiv (⊥ : Fx) Γ₀ Γdec.toBoundCtx t s outputSort := by
  let p := decision probeEarlier
  let q := decision (probeLater false)
  have hp := decision_typed probeEarlier earlier_typed
  have hq := decision_typed (probeLater false) (later_typed false)
  obtain ⟨t, ht, _⟩ := (Response.DecisionTree.source_wf sig pureDecisionCtx strict p hp).toLetIter
  obtain ⟨s, hs, _⟩ := (Response.DecisionTree.source_wf sig pureDecisionCtx strict q hq).toLetIter
  exact ⟨t, s, ht, hs, fun h => decisionSourceDiffers
    ((Response.DecisionTree.endpoint_reflection sig pureDecisionCtx strict p q hp hq ht hs).mp h)⟩

end EffectfulDecisionTree

section ReorderedDecisionTree

open Response.DecisionTree (Shape Program)

abbrev Γmix : EffectCtx T Fx :=
  [(Ty.coprod inputSort inputSort, ⊥), (outputSort, ⊥), (Ty.coprod inputSort inputSort, ⊥)]
abbrev Γhead := SumSplit.branchCtx Γmix 0 inputSort
abbrev Γtail := SumSplit.branchCtx Γmix 2 inputSort

abbrev headNext : Fin Γhead.length := ⟨2, by decide⟩
abbrev tailNext : Fin Γtail.length := ⟨0, by decide⟩
abbrev headArm : Shape Γhead := .split headNext rfl (finalShape false) (finalShape false)
abbrev tailArm : Shape Γtail := .split tailNext rfl (finalShape false) (finalShape false)
abbrev headFirst : Shape Γmix := .split 0 rfl headArm headArm
abbrev tailFirst : Shape Γmix := .split 2 rfl tailArm tailArm

abbrev twice (rev : Bool) : Response.Flatten.Program sig (decisionSlots false) true :=
  if rev then
    .let1 (probeLater false) (.request Prim.read (fun _ =>
      Tree.var (S := sig) (sorts := Response.extendSorts true (decisionSlots false)) 1))
  else
    .let1 probeEarlier (.request Prim.read (fun _ =>
      Tree.var (S := sig) (sorts := Response.extendSorts true (decisionSlots false)) 3))

private theorem twice_typed (rev : Bool) : Response.Flatten.Program.WellTyped sig strict (twice rev) := by
  cases rev <;> exact ⟨⟨le_rfl, fun _ => trivial⟩, ⟨le_rfl, fun _ => trivial⟩⟩

abbrev headProgram (a : Bool) : Program sig true headArm :=
  .split headNext (.leaf (twice a)) (.leaf (twice (!a)))
abbrev tailProgram (b : Bool) : Program sig true tailArm :=
  .split tailNext (.leaf (twice b)) (.leaf (twice (!b)))
abbrev pqHead : Program sig true headFirst := .split 0 (headProgram false) (headProgram true)
abbrev pqTail : Program sig true tailFirst := .split 2 (tailProgram false) (tailProgram true)

private theorem mixPure : Γmix.Pure := by unfold EffectCtx.Pure; decide
private theorem headTyped : Program.WellTyped sig strict pqHead :=
  ⟨⟨twice_typed false, twice_typed true⟩, ⟨twice_typed true, twice_typed false⟩⟩
private theorem tailTyped : Program.WellTyped sig strict pqTail :=
  ⟨⟨twice_typed false, twice_typed true⟩, ⟨twice_typed true, twice_typed false⟩⟩

private def requests : Expr Prim → Option (Nat × Nat)
  | .let₁ (.op .read (.pair (.var i) .unit)) (.op .read (.pair (.var j) .unit)) =>
      some (i, j - 1)
  | _ => none

-- Inspect the actual two requests after both splits, including removal of the
-- first response binder from the second request's index.
example : requests (twice false).source = some (0, 2) := rfl
example : requests (twice true).source = some (2, 0) := rfl

private theorem mixedEqv : Eqv Γmix outputSort strict pqHead.source pqTail.source := by
  have wp := Response.DecisionTree.source_wf sig mixPure strict pqHead headTyped
  have wq := Response.DecisionTree.source_wf sig mixPure strict pqTail tailTyped
  have hΓ : Γhead.Pure := SumSplit.branchCtx_pure mixPure 0 inputSort
  have wh (a : Bool) : Wf Γhead (headProgram a).source outputSort strict :=
    Response.DecisionTree.source_wf sig hΓ strict (headProgram a)
      ⟨twice_typed a, twice_typed (!a)⟩
  have eL := SumSplit.caseArms_left (Γ := Γmix) (i := 0) rfl rfl (wh false) (wh true)
  have eR := SumSplit.caseArms_right (Γ := Γmix) (i := 0) rfl rfl (wh false) (wh true)
  have hLeaf (rev : Bool) :
      Wf (SumSplit.branchCtx Γhead 2 inputSort) (twice rev).source outputSort strict :=
    source_wf sig (SumSplit.branchCtx_pure hΓ headNext inputSort) (leafSlots_typed false)
      strict (twice rev) (twice_typed rev)
  have hL0 := SumSplit.caseArms_left (i := tailNext) rfl rfl (hLeaf false) (hLeaf true)
  have hR0 := SumSplit.caseArms_right (i := tailNext) rfl rfl (hLeaf false) (hLeaf true)
  have hL1 := SumSplit.caseArms_left (i := tailNext) rfl rfl (hLeaf true) (hLeaf false)
  have hR1 := SumSplit.caseArms_right (i := tailNext) rfl rfl (hLeaf true) (hLeaf false)
  refine (SumSplit.eqv_iff_specializations (i := 0) rfl rfl wp wq).mpr ⟨?_, ?_⟩
  · refine eL.trans ?_
    exact (SumSplit.caseArms_eqv_iff headNext rfl rfl (hLeaf false) (hLeaf true)
      hL0.endpoints_wf.1 hL1.endpoints_wf.1).mpr ⟨hL0.symm, hL1.symm⟩
  · refine eR.trans ?_
    exact (SumSplit.caseArms_eqv_iff headNext rfl rfl (hLeaf true) (hLeaf false)
      hR0.endpoints_wf.1 hR1.endpoints_wf.1).mpr ⟨hR0.symm, hR1.symm⟩

/-- Opposite test orders agree at the strict bound. Both the native equality
and its mixed-shape reflection are checked on these concrete programs. -/
example : ∃ t s : Tm Empty Prim Γmix.length,
    pqHead.source.toLetIter Γmix.length = some t ∧ pqTail.source.toLetIter Γmix.length = some s ∧
    AbortEquiv (⊥ : Fx) Γ₀ Γmix.toBoundCtx t s outputSort ∧
    Eqv Γmix outputSort strict pqHead.source pqTail.source := by
  obtain ⟨t, ht, _⟩ := mixedEqv.endpoints_wf.1.toLetIter
  obtain ⟨s, hs, _⟩ := mixedEqv.endpoints_wf.2.toLetIter
  have hn := mixedEqv.toLetIter ht hs
  exact ⟨t, s, ht, hs, hn, (Response.DecisionTree.Reorder.endpoint_reflection sig mixPure
    strict pqHead pqTail headTyped tailTyped ht hs).mp hn⟩

end ReorderedDecisionTree

section EffectfulSumScrutinee

open Response (Atom extendSorts)
open Response.SumCall (SumSignature Program SumArgs SumResponse)

abbrev sumSig : SumSignature Bool Unit :=
  ⟨fun _ => 1, fun _ _ => false, fun _ => false, fun _ => true⟩

local instance : HasEff Unit Fx := ⟨fun _ => strict⟩
local instance : HasEff (Prim ⊕ Unit) Fx := Response.SumCall.effects
local instance : HasTy (Prim ⊕ Unit) T := Response.SumCall.endpoints sig sumSig

abbrev outerArgs : SumArgs sig sumSig sorts () := fun _ => .var 1
abbrev leftResponseArm : Response.Sequence sig true (extendSorts false sorts) :=
  .call Prim.read (fun _ => .var 0) (.ret (.var 0))
abbrev rightResponseArm (next : Bool) : Response.Sequence sig true (extendSorts true sorts) :=
  .call Prim.readOther (fun _ => .var 0)
    (if next then .call Prim.readAlt (fun _ => .var 0) (.ret (.var 0))
      else .call Prim.read (fun _ => .var 0) (.ret (.var 0)))
abbrev sumProgram (next : Bool) : Program sig sumSig sorts true :=
  ⟨(), outerArgs, leftResponseArm, rightResponseArm next⟩

private theorem outerVisible (g : Unit) : ¬ IsPure (⊥ : Fx) g := by
  change strict ≠ (⊥ : Fx)
  decide

private theorem sumTyped (next : Bool) : Program.WellTyped sig sumSig strict (sumProgram next) := by
  have hr : ¬ IsPure (⊥ : Fx) Prim.readAlt := by
    change strict ≠ (⊥ : Fx)
    decide
  cases next
  · exact ⟨fun _ => trivial, le_rfl,
      ⟨fun _ => trivial, read_not_pure, le_rfl, trivial⟩,
      ⟨fun _ => trivial, read_other_not_pure, le_rfl,
        fun _ => trivial, read_not_pure, le_rfl, trivial⟩⟩
  · exact ⟨fun _ => trivial, le_rfl,
      ⟨fun _ => trivial, read_not_pure, le_rfl, trivial⟩,
      ⟨fun _ => trivial, read_other_not_pure, le_rfl,
        fun _ => trivial, hr, le_rfl, trivial⟩⟩

/-- Observe exactly one outer request, then distinct first requests in the two
arms. The right arm uses its first call's response in its next request. -/
example :
    ∃ d : Derivation (Prim ⊕ Unit) Γ₀ Γ.toBoundCtx (sumProgram true).native outputSort,
    ∃ k : SumResponse sig sumSig sorts () →
        ITree.Tree (Response.SumCall.Event sig sumSig sorts) (Atom sig sorts true),
      d.denote (Ty.denote (Atom sig sorts)) (Response.SumCall.instructions (ε := Fx) sig sumSig sorts)
          (fun x => x.elim) (Response.variableEnv sig sorts slots_typed Tree.var) =
          ITree.vis (.sum () outerArgs) k ∧
      (∀ a, k (.inl a) = ITree.vis (.atom Prim.read (fun _ => a)) (fun b => ITree.ret ⟨b⟩)) ∧
      (∀ a, k (.inr a) = ITree.vis (.atom Prim.readOther (fun _ => a)) (fun b =>
        ITree.vis (.atom Prim.readAlt (fun _ => b)) (fun c => ITree.ret ⟨c⟩))) := by
  obtain ⟨d, hd⟩ := Response.SumCall.eval_exists sig sumSig sorts slots_typed strict
    (sumProgram true) (sumTyped true)
  exact ⟨d, _, (hd Tree.var).trans rfl, fun _ => rfl, fun _ => rfl⟩

private def secondRequest {n : Nat} {ss : Fin n → Bool} : Response.Sequence sig true ss → Option Prim
  | .call _ _ (.call f _ _) => some f
  | _ => none

/-- Equal outer requests and equal left arms still expose the changed second
request of the right arm. This runs through native soundness and both tagged
response observations at the strict bound. -/
example : ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx
    (sumProgram true).native (sumProgram false).native outputSort := by
  intro h
  have he := Response.SumCall.native_eq_implies_eq sig sumSig outerVisible slots_typed strict
    (sumProgram true) (sumProgram false) (sumTyped true) (sumTyped false) h
  have hs : some Prim.readAlt = some Prim.read :=
    congrArg (fun (p : Program sig sumSig sorts true) => secondRequest p.right) he
  cases hs

example : AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx
    (sumProgram true).native (sumProgram false).native outputSort ↔
    Eqv Γ outputSort strict (sumProgram true).source (sumProgram false).source :=
  Response.SumCall.endpoint_reflection sig sumSig outerVisible ctx_pure slots_typed strict
    (sumProgram true) (sumProgram false) (sumTyped true) (sumTyped false)

section ResponseDependentRequest

abbrev afterRead := extendSorts false sorts

abbrev subsequentArgs (fromReply : Bool) : SumArgs sig sumSig afterRead () :=
  if fromReply then fun _ => .var 0 else fun _ => .var 2

abbrev mixedProgram (fromReply : Bool) : Response.Mixed.Program sig sumSig true sorts :=
  .atom Prim.readOther (fun _ => .var 0)
    (.sum () (subsequentArgs fromReply)
      (.atom Prim.read (fun _ => .var 0) (.ret (.var 0)))
      (.atom Prim.readOther (fun _ => .var 0)
        (.atom Prim.readAlt (fun _ => .var 0) (.ret (.var 0)))))

private theorem mixedTyped (fromReply : Bool) :
    Response.Mixed.Program.WellTyped sig sumSig strict (mixedProgram fromReply) := by
  have hAlt : ¬ IsPure (⊥ : Fx) Prim.readAlt := by
    change strict ≠ (⊥ : Fx)
    decide
  have hArgs : ∀ i, DeclaredPure (ε := Fx) sig (subsequentArgs fromReply i) := by
    cases fromReply <;> exact fun _ => trivial
  exact ⟨fun _ => trivial, read_other_not_pure, le_rfl, hArgs, le_rfl,
    ⟨fun _ => trivial, read_not_pure, le_rfl, trivial⟩,
    ⟨fun _ => trivial, read_other_not_pure, le_rfl, fun _ => trivial, hAlt, le_rfl, trivial⟩⟩

/-- The second visible request uses the actual first reply as its argument.
The response tag of that request then chooses the next request. -/
example :
    ∃ d : Derivation (Prim ⊕ Unit) Γ₀ Γ.toBoundCtx (mixedProgram true).native outputSort,
    ∃ k : Tree sig sorts false →
        ITree.Tree (Response.SumCall.Event sig sumSig sorts) (Atom sig sorts true),
      d.denote (Ty.denote (Atom sig sorts)) (Response.SumCall.instructions (ε := Fx) sig sumSig sorts)
          (fun x => x.elim) (Response.variableEnv sig sorts slots_typed Tree.var) =
          ITree.vis (.atom Prim.readOther (fun _ => Tree.var 0)) k ∧
      ∀ reply, ∃ branch : SumResponse sig sumSig sorts () →
          ITree.Tree (Response.SumCall.Event sig sumSig sorts) (Atom sig sorts true),
        k reply = ITree.vis (.sum () (fun _ => reply)) branch ∧
        (∀ a, branch (.inl a) = ITree.vis (.atom Prim.read (fun _ => a)) (fun b => ITree.ret ⟨b⟩)) ∧
        (∀ a, branch (.inr a) = ITree.vis (.atom Prim.readOther (fun _ => a)) (fun b =>
          ITree.vis (.atom Prim.readAlt (fun _ => b)) (fun c => ITree.ret ⟨c⟩))) := by
  obtain ⟨d, hd⟩ := Response.Mixed.eval_exists sig sumSig sorts slots_typed strict
    (mixedProgram true) (mixedTyped true)
  exact ⟨d, _, (hd Tree.var).trans rfl, fun _ => ⟨_, rfl, fun _ => rfl, fun _ => rfl⟩⟩

private def treeSlot {n : Nat} {ss : Fin n → Bool} {a : Bool} : Tree sig ss a → Option Nat
  | .var i => some i.val
  | .op _ _ => none

private def sumArgSlot : Response.Mixed.Program sig sumSig true sorts → Option Nat
  | .atom _ _ (.sum _ args _ _) => treeSlot (args 0)
  | _ => none

private theorem reply_distinguished :
    ¬ AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx (mixedProgram true).native
      (mixedProgram false).native outputSort := by
  intro h
  have he := Response.Mixed.native_eq_implies_eq sig sumSig outerVisible slots_typed strict
    (mixedProgram true) (mixedProgram false) (mixedTyped true) (mixedTyped false) h
  have hslots : (some 0 : Option Nat) = some 2 := congrArg sumArgSlot he
  cases hslots

/-- Replacing the response by an ambient variable of the same sort changes
the source class at the same strict bound. -/
example : ¬ Eqv Γ outputSort strict (mixedProgram true).source (mixedProgram false).source := by
  intro he
  exact reply_distinguished ((Response.Mixed.endpoint_reflection sig sumSig outerVisible ctx_pure
    slots_typed strict (mixedProgram true) (mixedProgram false) (mixedTyped true) (mixedTyped false)).mpr he)

end ResponseDependentRequest

section RawSumResponseArms


abbrev payloadRead : Response.Flatten.Program sig (extendSorts true sorts) false :=
  .request Prim.readOther (fun _ => .var 0)
abbrev argumentRead : Response.Flatten.Program sig (extendSorts false (extendSorts true sorts)) true :=
  .request Prim.readAlt (fun _ => .var 0)
abbrev nestedRaw : Response.Mixed.RawArms.Program sig sumSig sorts true :=
  ⟨(), outerArgs, .request Prim.read (fun _ => .var 0), .unary Prim.readAlt rfl payloadRead⟩
abbrev sequencedRaw : Response.Mixed.RawArms.Program sig sumSig sorts true :=
  ⟨(), outerArgs, .request Prim.read (fun _ => .var 0), .let1 payloadRead argumentRead⟩

private theorem nestedRaw_typed : Response.Mixed.RawArms.Program.WellTyped sig sumSig strict nestedRaw :=
  ⟨fun _ => trivial, le_rfl, ⟨le_rfl, fun _ => trivial⟩, le_rfl, le_rfl, fun _ => trivial⟩
private theorem sequencedRaw_typed : Response.Mixed.RawArms.Program.WellTyped sig sumSig strict sequencedRaw :=
  ⟨fun _ => trivial, le_rfl, ⟨le_rfl, fun _ => trivial⟩,
    ⟨le_rfl, fun _ => trivial⟩, le_rfl, fun _ => trivial⟩

private theorem sameArmCompile : Response.Flatten.compile (ε := Fx) sig nestedRaw.right =
    Response.Flatten.compile (ε := Fx) sig sequencedRaw.right := by
  have hArgs :
      Response.Flatten.unaryArgs sig (f := Prim.readAlt) rfl
        (Tree.var (S := sig) (sorts := extendSorts false (extendSorts true sorts)) 0) =
      (fun _ => Tree.var (S := sig) (sorts := extendSorts false (extendSorts true sorts)) 0) := by
    funext i
    rw [Fin.eq_zero i]
    rfl
  simp only [nestedRaw, sequencedRaw, Response.Flatten.compile, Response.Flatten.unaryTail, hArgs]

private theorem sameCompile : Response.Mixed.RawArms.Program.compile (ε := Fx) sig sumSig nestedRaw =
    Response.Mixed.RawArms.Program.compile (ε := Fx) sig sumSig sequencedRaw := by
  exact congrArg (fun arm => Response.Mixed.Program.sum (S := sig) (T := sumSig) () outerArgs
    (Response.Mixed.ofSequence sig sumSig (Response.Flatten.compile (ε := Fx) sig nestedRaw.left))
    (Response.Mixed.ofSequence sig sumSig arm)) sameArmCompile

/-- The raw lowering passes the selected right payload to readOther, nested
inside the argument of readAlt. -/
example : nestedRaw.source.toLetIter Γ.length = some
    (.case (.op (.inr ()) (.pair (.bv 1) .unit))
      (.op (.inl Prim.read) (.pair (.bv 0) .unit))
      (.op (.inl Prim.readAlt) (.pair (.op (.inl Prim.readOther) (.pair (.bv 0) .unit)) .unit))) :=
  rfl

/-- The inner read uses the payload at slot zero. Its response becomes
the argument of the second request. -/
example : Response.Flatten.compile (ε := Fx) sig nestedRaw.right = rightResponseArm true := by
  rw [sameArmCompile]
  simp only [sequencedRaw, Response.Flatten.compile, Response.Flatten.emit,
    ite_eq_right read_other_not_pure, ite_eq_right read_alt_not_pure,
    Response.Sequence.bind, Response.Sequence.subst]
  rfl

/-- The explicit let and the nested argument are equal at the strict bound.
Both native endpoints keep that bound, and the raw endpoint theorem reflects
their equality. -/
example : ∃ t s : Tm Empty (Prim ⊕ Unit) Γ.length,
    nestedRaw.source.toLetIter Γ.length = some t ∧ sequencedRaw.source.toLetIter Γ.length = some s ∧
    HasTypeEffect Γ₀ Γ.toBoundCtx t outputSort strict ∧ HasTypeEffect Γ₀ Γ.toBoundCtx s outputSort strict ∧
    AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx t s outputSort ∧
    Eqv Γ outputSort strict nestedRaw.source sequencedRaw.source := by
  let h := Response.Mixed.RawArms.source_wf sig sumSig (c := true) ctx_pure slots_typed strict
  obtain ⟨t, ht, _⟩ := (h nestedRaw nestedRaw_typed).toLetIter
  obtain ⟨s, hs, _⟩ := (h sequencedRaw sequencedRaw_typed).toLetIter
  obtain ⟨hpt, _, hp⟩ := Response.Mixed.RawArms.compile_native sig sumSig ctx_pure slots_typed strict
    nestedRaw nestedRaw_typed ht
  obtain ⟨hqt, _, hq⟩ := Response.Mixed.RawArms.compile_native sig sumSig ctx_pure slots_typed strict
    sequencedRaw sequencedRaw_typed hs
  have hq' := sameCompile.symm ▸ hq
  have hn := hp.trans hq'.symm
  exact ⟨t, s, ht, hs, hpt, hqt, hn,
    (Response.Mixed.RawArms.endpoint_reflection sig sumSig outerVisible ctx_pure slots_typed strict
      nestedRaw sequencedRaw nestedRaw_typed sequencedRaw_typed ht hs).mp hn⟩

end RawSumResponseArms

section RawMixedPrefix

abbrev argumentInLeft : Response.Flatten.Program sig (extendSorts false sorts) false :=
  .unary Prim.readOther rfl (.request Prim.read (fun _ => .var 0))

abbrev secondLeft : Response.Mixed.Raw.Program sig sumSig true (extendSorts false (extendSorts false sorts)) :=
  .straight (.request Prim.readAlt (fun _ => .var 1))
abbrev secondRight : Response.Mixed.Raw.Program sig sumSig true (extendSorts true (extendSorts false sorts)) :=
  .straight (.tree (.var 0))
abbrev shiftedLeft : Response.Mixed.Raw.Program sig sumSig true
    (extendSorts false (extendSorts false (extendSorts false sorts))) :=
  .straight (.request Prim.readAlt (fun _ => .var 2))
abbrev shiftedRight : Response.Mixed.Raw.Program sig sumSig true
    (extendSorts true (extendSorts false (extendSorts false sorts))) :=
  .straight (.tree (.var 0))

abbrev nestedInLeft : Response.Mixed.Raw.Program sig sumSig true (extendSorts false sorts) :=
  .sumUnary () rfl argumentInLeft secondLeft secondRight
abbrev explicitInLeft : Response.Mixed.Raw.Program sig sumSig true (extendSorts false sorts) :=
  .let1 argumentInLeft (.sum () (fun _ => .var 0) shiftedLeft shiftedRight)

abbrev rawNestedTree : Response.Mixed.Raw.Program sig sumSig true sorts :=
  .sum () outerArgs nestedInLeft (.straight (.tree (.var 0)))
abbrev rawPrefixTree : Response.Mixed.Raw.Program sig sumSig true sorts :=
  .sum () outerArgs explicitInLeft (.straight (.tree (.var 0)))

private theorem rawNestedTree_typed : Response.Mixed.Raw.Program.WellTyped sig sumSig strict rawNestedTree := by
  refine ⟨fun _ => trivial, le_rfl, ?_, trivial⟩
  exact ⟨⟨le_rfl, le_rfl, fun _ => trivial⟩, le_rfl, ⟨le_rfl, fun _ => trivial⟩, trivial⟩

private theorem rawPrefixTree_typed : Response.Mixed.Raw.Program.WellTyped sig sumSig strict rawPrefixTree := by
  refine ⟨fun _ => trivial, le_rfl, ?_, trivial⟩
  exact ⟨⟨le_rfl, le_rfl, fun _ => trivial⟩, fun _ => trivial, le_rfl, ⟨le_rfl, fun _ => trivial⟩, trivial⟩

private theorem rawMixedSameCompile :
    Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig rawNestedTree =
      Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig rawPrefixTree := by
  have ha : Response.Mixed.Raw.unaryVarArgs sig sumSig (g := ()) (slots := extendSorts false sorts) rfl =
      (fun _ => .var 0) := by
    funext i
    rw [Fin.eq_zero i]
    rfl
  have hl : Response.Mixed.weakenUnder sig sumSig false
      (Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig secondLeft) =
      Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig shiftedLeft := by
    simp only [Response.Mixed.Raw.Program.compile, Response.Flatten.compile,
      Response.Flatten.emit, ite_eq_right read_alt_not_pure, Response.Mixed.ofSequence,
      Response.Mixed.weakenUnder, Response.Mixed.subst]
    rfl
  have hr : Response.Mixed.weakenUnder sig sumSig false
      (Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig secondRight) =
      Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig shiftedRight := rfl
  have hbody :
      (Response.Mixed.Program.sum (S := sig) (T := sumSig) ()
        (Response.Mixed.Raw.unaryVarArgs sig sumSig (slots := extendSorts false sorts) rfl)
        (Response.Mixed.weakenUnder sig sumSig false
          (Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig secondLeft))
        (Response.Mixed.weakenUnder sig sumSig false
          (Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig secondRight))) =
      .sum () (fun _ => .var 0) (Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig shiftedLeft)
        (Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig shiftedRight) := by
    rw [ha, hl, hr]
  exact congrArg (fun body => Response.Mixed.Program.sum (S := sig) (T := sumSig) () outerArgs
    (Response.Mixed.bindPrefix sig sumSig (Response.Flatten.compile (ε := Fx) sig argumentInLeft) body)
    (.ret (.var 0))) hbody

/-- A second sum request is inside the first left arm. Its argument contains
two nested atomic calls and uses that first payload at slot zero. -/
example : rawNestedTree.source.toLetIter Γ.length = some
    (.case (.op (.inr ()) (.pair (.bv 1) .unit))
      (.case (.op (.inr ())
        (.pair (.op (.inl Prim.readOther) (.pair (.op (.inl Prim.read) (.pair (.bv 0) .unit)) .unit)) .unit))
        (.op (.inl Prim.readAlt) (.pair (.bv 1) .unit)) (.bv 0))
      (.bv 0)) := rfl

private def compiledLeftRequests (p : Response.Mixed.Program sig sumSig true sorts) : List (Option Nat) :=
  match p with
  | .sum _ _ (.atom .read first (.atom .readOther next (.sum _ arg (.atom .readAlt retained _) _))) _ =>
    [treeSlot (first 0), treeSlot (next 0), treeSlot (arg 0), treeSlot (retained 0)]
  | _ => []

/-- The normalized branch passes each new reply into the next request.
After the second split, slot three still points to the first sum payload. -/
example : compiledLeftRequests (Response.Mixed.Raw.Program.compile (ε := Fx) sig sumSig rawNestedTree) =
    [some 0, some 0, some 0, some 3] := by
  simp only [Response.Mixed.Raw.Program.compile, Response.Flatten.compile, Response.Flatten.unaryTail,
    Response.Flatten.emit, ite_eq_right read_not_pure, ite_eq_right read_other_not_pure,
    ite_eq_right read_alt_not_pure, Response.Sequence.bind, Response.Sequence.subst,
    Response.Mixed.bindPrefix, Response.Mixed.ofSequence, Response.Mixed.weakenUnder, Response.Mixed.subst]
  rfl

/-- Both raw trees stay at the strict bound, including the nested argument
and the arm that retains the earlier payload. -/
example : ∃ t s : Tm Empty (Prim ⊕ Unit) Γ.length,
    rawNestedTree.source.toLetIter Γ.length = some t ∧ rawPrefixTree.source.toLetIter Γ.length = some s ∧
    HasTypeEffect Γ₀ Γ.toBoundCtx t outputSort strict ∧ HasTypeEffect Γ₀ Γ.toBoundCtx s outputSort strict ∧
    AbortEquiv (⊥ : Fx) Γ₀ Γ.toBoundCtx t s outputSort ∧
    Eqv Γ outputSort strict rawNestedTree.source rawPrefixTree.source := by
  let h := Response.Mixed.Raw.source_wf sig sumSig (c := true) ctx_pure slots_typed strict
  obtain ⟨t, ht, _⟩ := (h rawNestedTree rawNestedTree_typed).toLetIter
  obtain ⟨s, hs, _⟩ := (h rawPrefixTree rawPrefixTree_typed).toLetIter
  obtain ⟨ht', _, hp⟩ := Response.Mixed.Raw.compile_native sig sumSig ctx_pure slots_typed strict
    rawNestedTree rawNestedTree_typed ht
  obtain ⟨hs', _, hq⟩ := Response.Mixed.Raw.compile_native sig sumSig ctx_pure slots_typed strict
    rawPrefixTree rawPrefixTree_typed hs
  have hq' := rawMixedSameCompile.symm ▸ hq
  have hn := hp.trans hq'.symm
  exact ⟨t, s, ht, hs, ht', hs', hn,
    (Response.Mixed.Raw.endpoint_reflection sig sumSig outerVisible ctx_pure slots_typed strict
      rawNestedTree rawPrefixTree rawNestedTree_typed rawPrefixTree_typed ht hs).mp hn⟩

end RawMixedPrefix

end EffectfulSumScrutinee

end LetIterResponseSingleCall

namespace LetIterRankedFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response

abbrev Fx := Bool × Bool
abbrev strict : Fx := (true, false)
abbrev A : Ty Unit := .base ()
abbrev X : Ty Unit := .coprod .unit .unit
abbrev R : Ty Unit := .coprod A X
abbrev sig : Signature Unit Empty := ⟨Empty.elim, fun e => e.elim, Empty.elim⟩
abbrev sumSig : SumCall.SumSignature Unit Unit := ⟨fun _ => 0, fun _ i => i.elim0, fun _ => (), fun _ => ()⟩
abbrev free := (Ctx.nil : Ctx Empty (Ty Unit))
abbrev Term n := Tm Empty (Empty ⊕ Unit) n

local instance : HasEff Empty Fx := ⟨Empty.elim⟩
local instance : HasEff Unit Fx := ⟨fun _ => strict⟩
local instance : HasEff (Empty ⊕ Unit) Fx := SumCall.effects
local instance : HasTy (Empty ⊕ Unit) (Ty Unit) := SumCall.endpoints sig sumSig
local instance : EffectIteration Fx := EffectIteration.complete Fx

abbrev state (i : Bool) (n : Nat) : Term n :=
  if i then .inr .unit else .inl .unit
abbrev ask (n : Nat) : Term n := .op (.inr ()) .unit

-- The `true` state repeats on the right reply, while the `false` state
-- makes its own request and exits on either reply.
abbrev replyStep (i : Bool) (n : Nat) : Term n :=
  .case (ask n) (.inl (.bv 0)) (if i then .inr (state false (n + 1)) else .inl (.bv 0))
abbrev loopBody (n : Nat) : Term (n + 1) :=
  .case (.bv 0) (replyStep false (n + 2)) (replyStep true (n + 2))
abbrev loop (i : Bool) (n : Nat) : Term n := .iter (state i n) (loopBody n)
abbrev restart (n : Nat) : Term (n + 1) := .iter (.bv 0) (loopBody (n + 1))
abbrev dispatch (n : Nat) : Term (n + 1) := .case (.bv 0) (.bv 0) (restart (n + 1))

private theorem stateTy {n : Nat} (β : BoundCtx (Ty Unit) n) (i : Bool) :
    HasType (Empty ⊕ Unit) free β (state i n) X := by
  cases i
  · exact .inl .unit
  · exact .inr .unit

private theorem replyTy {n : Nat} (β : BoundCtx (Ty Unit) n) (i : Bool) :
    HasType (Empty ⊕ Unit) free β (replyStep i n) R := by
  cases i
  · exact .case (.op .unit) (.inl .bv) (.inl .bv)
  · exact .case (.op .unit) (.inl .bv) (.inr (.inl .unit))

private theorem bodyTy {n : Nat} (β : BoundCtx (Ty Unit) n) :
    HasType (Empty ⊕ Unit) free (.snoc β X) (loopBody n) R :=
  .case (A := (Ty.unit : Ty Unit)) (B := Ty.unit) .bv (replyTy _ false) (replyTy _ true)

private theorem restartTy {n : Nat} (β : BoundCtx (Ty Unit) n) :
    HasType (Empty ⊕ Unit) free (.snoc β X) (restart n) A :=
  .iter .bv (bodyTy _)

private theorem dispatchTy {n : Nat} (β : BoundCtx (Ty Unit) n) :
    HasType (Empty ⊕ Unit) free (.snoc β R) (dispatch n) A :=
  .case (A := A) (B := X) .bv .bv (restartTy _)

private theorem selectState {n : Nat} (β : BoundCtx (Ty Unit) n) (i : Bool) :
    Equiv (⊥ : Fx) free β
      (.case (state i n) (replyStep false (n + 1)) (replyStep true (n + 1))) (replyStep i n) R := by
  cases i
  · exact (Equiv.caseBetaL (B := (Ty.unit : Ty Unit)) .unit (replyTy _ false) (replyTy _ true)).trans
      (Equiv.letBeta .unit .unit (replyTy _ false))
  · exact (Equiv.caseBetaR (A := (Ty.unit : Ty Unit)) .unit (replyTy _ false) (replyTy _ true)).trans
      (Equiv.letBeta .unit .unit (replyTy _ true))

private theorem unfoldLoop {n : Nat} (β : BoundCtx (Ty Unit) n) (i : Bool) :
    Equiv (⊥ : Fx) free β (loop i n) (.case (replyStep i n) (.bv 0) (restart n)) A := by
  have hfix := Equiv.fixpoint (pureEff := (⊥ : Fx)) (stateTy β i) (bodyTy β)
  have hp : Pure (⊥ : Fx) (state i n) := by
    cases i
    · exact .inl .unit
    · exact .inr .unit
  have hw : HasType (Empty ⊕ Unit) free (.snoc β X)
      (.case (loopBody n) (.bv 0) (restart (n + 1))) A :=
    .case (A := A) (B := X) (bodyTy β) .bv (restartTy _)
  have h₁ := hfix.trans (Equiv.letBeta hp (stateTy β i) hw)
  exact h₁.trans (.case (selectState β i) (.refl .bv) (.refl (restartTy β)))

abbrev replyLeft (n : Nat) : Term (n + 1) := .inl (.bv 0)
abbrev replyRight (i : Bool) (n : Nat) : Term (n + 1) :=
  if i then .inr (state false (n + 1)) else replyLeft n

private theorem leftTy {n : Nat} (β : BoundCtx (Ty Unit) n) :
    HasType (Empty ⊕ Unit) free (.snoc β A) (replyLeft n) R :=
  .inl .bv

private theorem rightTy {n : Nat} (β : BoundCtx (Ty Unit) n) (i : Bool) :
    HasType (Empty ⊕ Unit) free (.snoc β A) (replyRight i n) R := by
  cases i
  · exact leftTy β
  · exact .inr (stateTy _ false)

private theorem returnReply {n : Nat} (β : BoundCtx (Ty Unit) n) :
    Equiv (⊥ : Fx) free (.snoc β A) (.let₁ (replyLeft n) (dispatch (n + 1))) (.bv 0) A := by
  have h := Equiv.letBeta (pureEff := (⊥ : Fx)) (.inl .bv) (leftTy β) (dispatchTy (.snoc β A))
  exact h.trans ((Equiv.caseBetaL (.bv (ι := 0)) .bv (restartTy _)).trans (Equiv.letEta .bv))

private theorem repeatReply {n : Nat} (β : BoundCtx (Ty Unit) n) :
    Equiv (⊥ : Fx) free (.snoc β A) (.let₁ (replyRight true n) (dispatch (n + 1))) (loop false (n + 1)) A := by
  have h := Equiv.letBeta (pureEff := (⊥ : Fx)) (.inr (.inl .unit)) (rightTy β true) (dispatchTy (.snoc β A))
  have hcase := Equiv.caseBetaR (pureEff := (⊥ : Fx)) (A := A)
    (stateTy (.snoc β A) false) (.bv (ι := 0)) (restartTy (.snoc β A))
  have hbeta := Equiv.letBeta (pureEff := (⊥ : Fx)) (.inl .unit)
    (stateTy (.snoc β A) false) (restartTy (.snoc β A))
  exact h.trans (hcase.trans hbeta)

private theorem simplifyReply {n : Nat} (β : BoundCtx (Ty Unit) n) (i : Bool) :
    Equiv (⊥ : Fx) free β (.case (replyStep i n) (.bv 0) (restart n))
      (.case (ask n) (.bv 0) (if i then loop false (n + 1) else .bv 0)) A := by
  have h :=
    Equiv.bindCase (pureEff := (⊥ : Fx)) (replyTy β i) (.bv (ι := 0)) (restartTy β)
  have hAsk : HasType (Empty ⊕ Unit) free β (ask n) (.coprod A A) := .op .unit
  have h' := Equiv.bindLetCase (pureEff := (⊥ : Fx)) hAsk (leftTy β) (rightTy β i) (dispatchTy β)
  refine h.trans (h'.trans (.case (.refl hAsk) (returnReply β) ?_))
  cases i
  · exact returnReply β
  · exact repeatReply β

def rank : Bool → Nat
  | false => 0
  | true => 1

abbrev finish {n : Nat} {ss : Fin n → Unit} :
    Mixed.Raw.Program sig sumSig () (extendSorts () ss) := .straight (.tree (.var 0))

def sys : Mixed.Ranked.System sig sumSig rank () where
  endpoint := fun {n} _ i => loop i n
  step := fun _ i => match i with
    | false => .sum () (fun i => i.elim0) (.done finish) (.done finish)
    | true => .sum () (fun i => i.elim0) (.done finish) (.again false (by decide))

private theorem sumVisible (g : Unit) : ¬ IsPure (⊥ : Fx) g := by
  change strict ≠ (⊥ : Fx)
  decide

private theorem sys_checked : Mixed.Ranked.System.Checked sig sumSig rank sys strict := by
  refine ⟨?_, ?_, ?_⟩
  · intro n ss i
    cases i
    · exact ⟨fun j => j.elim0, le_rfl, trivial, trivial⟩
    · exact ⟨fun j => j.elim0, le_rfl, trivial, trivial⟩
  · intro Γ ss hΓ hs i
    refine ⟨.iter (stateTy Γ.toBoundCtx i) (bodyTy Γ.toBoundCtx), ?_⟩
    cases i <;> exact le_rfl
  · intro Γ ss hΓ hs i
    have h := (unfoldLoop Γ.toBoundCtx i).trans (simplifyReply Γ.toBoundCtx i)
    cases i
    · exact .equiv h
    · exact .equiv h

abbrev returnEither {n : Nat} {ss : Fin n → Unit} : Mixed.Raw.Program sig sumSig () ss :=
  .sum () (fun j => j.elim0) finish finish

/-- Only the right reply causes a second request, in the smaller state. -/
abbrev unrolled {n : Nat} {ss : Fin n → Unit} : Mixed.Raw.Program sig sumSig () ss :=
  .sum () (fun j => j.elim0) finish returnEither

private theorem unrolledTyped {n : Nat} (ss : Fin n → Unit) :
    Mixed.Raw.Program.WellTyped sig sumSig strict (unrolled (ss := ss)) :=
  ⟨fun j => j.elim0, le_rfl, trivial, fun j => j.elim0, le_rfl, trivial, trivial⟩

private theorem expandFalse {n : Nat} (ss : Fin n → Unit) :
    Mixed.Ranked.System.expand (ε := Fx) sig sumSig rank sys false ss =
      Mixed.Raw.Program.compile (ε := Fx) sig sumSig (returnEither (ss := ss)) := by
  rw [Mixed.Ranked.System.expand_step]
  rfl

private theorem expandTrue {n : Nat} (ss : Fin n → Unit) :
    Mixed.Ranked.System.expand (ε := Fx) sig sumSig rank sys true ss =
      Mixed.Raw.Program.compile (ε := Fx) sig sumSig (unrolled (ss := ss)) := by
  rw [Mixed.Ranked.System.expand_step]
  change Mixed.Program.sum (S := sig) (T := sumSig) () (fun j => j.elim0) (.ret (.var 0))
    (Mixed.Ranked.System.expand (ε := Fx) sig sumSig rank sys false (extendSorts () ss)) = _
  rw [expandFalse]
  rfl

abbrev Γ : EffectCtx (Ty Unit) Fx := []
abbrev slots : Fin Γ.length → Unit := Fin.elim0

/-- The local equation retains a native iteration only at the right reply. -/
example : Mixed.Ranked.Step.native (ε := Fx) sig sumSig rank sys.endpoint (sys.step slots true) =
    .case (ask Γ.length) (.bv 0) (loop false (Γ.length + 1)) :=
  rfl

/-- Native fixpoint expansion and source reflection at the strict effect
bound. The right tag of the first visible request takes the repeat site. -/
example : ∃ t : Term Γ.length, (unrolled (ss := slots)).source.toLetIter Γ.length = some t ∧
    HasTypeEffect free Γ.toBoundCtx (loop true Γ.length) A strict ∧
    HasTypeEffect free Γ.toBoundCtx t A strict ∧
    AbortEquiv (⊥ : Fx) free Γ.toBoundCtx (loop true Γ.length) t A ∧
    Eqv Γ A strict (Mixed.Ranked.System.expand (ε := Fx) sig sumSig rank sys true slots).source
      (unrolled (ss := slots)).source := by
  have hΓ : Γ.Pure := fun i => i.elim0
  have hs : ∀ i, (Γ.get i).1 = .base (slots i) := fun i => i.elim0
  let p := unrolled (ss := slots)
  have hp := unrolledTyped slots
  obtain ⟨t, ht, ht'⟩ := (Mixed.Raw.source_wf sig sumSig hΓ hs strict p hp).toLetIter
  have h := Mixed.Ranked.raw_endpoint_reflection sig sumSig rank sumVisible sys strict sys_checked
    true hΓ hs p hp ht
  have he : Eqv Γ A strict (Mixed.Ranked.System.expand (ε := Fx) sig sumSig rank sys true slots).source p.source := by
    rw [expandTrue]
    exact (Mixed.Raw.compile_eqv sig sumSig hΓ hs strict p hp).symm
  have htLoop := (Mixed.Ranked.expand_native sig sumSig rank sys strict sys_checked true hΓ hs).1
  exact ⟨t, ht, htLoop, ht', h.mpr he, h.mp (h.mpr he)⟩

end LetIterRankedFixture

namespace LetIterCompiledRankedFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response
open Mixed.Ranked.Compile

abbrev Fx := Bool × Bool
abbrev strict : Fx := (true, false)
abbrev sig : Signature Unit Unit := ⟨fun _ => 1, fun _ _ => (), fun _ => ()⟩
abbrev sumSig : SumCall.SumSignature Unit Unit :=
  ⟨fun _ => 0, fun _ i => i.elim0, fun _ => (), fun _ => ()⟩
abbrev A : Ty Unit := .base ()
abbrev free := (Ctx.nil : Ctx Empty (Ty Unit))
abbrev Γ : EffectCtx (Ty Unit) Fx := [(A, ⊥)]
abbrev slots : Fin Γ.length → Unit := fun _ => ()

local instance : HasEff Unit Fx := ⟨fun _ => strict⟩
local instance : HasEff (Unit ⊕ Unit) Fx := SumCall.effects
local instance : HasTy (Unit ⊕ Unit) (Ty Unit) := SumCall.endpoints sig sumSig
local instance : EffectIteration Fx := EffectIteration.complete Fx

private theorem visible (g : Unit) : ¬ IsPure (⊥ : Fx) g := by
  change strict ≠ (⊥ : Fx)
  decide

/-- State 1 branches on a visible sum reply. The right arm re-enters state 0
with that reply. The unary request of state 0 uses the carried payload. -/
def controller : Controller sig sumSig () () 1 :=
  Fin.cases (motive := fun j => Body sig sumSig () () 1 j.val (fun _ : Fin 1 => ()))
    (.atom () (fun _ => .var 0) (.done (.var 0)))
    (fun j => .sum () (fun i => i.elim0) (.done (.var 0))
      (.again 0 (Nat.zero_lt_succ j.val) (.var 0)))

private theorem controllerTyped (j : Fin 2) : Body.WellTyped sig sumSig strict (controller j) := by
  refine Fin.cases (motive := fun j => Body.WellTyped sig sumSig strict (controller j)) ?_ ?_ j
  · exact ⟨fun _ => trivial, visible (), le_rfl, trivial⟩
  · exact fun _ => ⟨fun i => i.elim0, le_rfl, trivial, trivial⟩

def start : Entry sig Fx () 1 slots := ⟨(0 : Fin 1).succ, .var 0, by trivial⟩

def afterReply : Entry sig Fx () 1 (extendSorts () slots) := ⟨0, .var 0, by trivial⟩

abbrev system := controller.system sig sumSig strict controllerTyped

private theorem stepStart :
    system.step slots start =
      .sum () (fun j => j.elim0) (.done (.straight (.tree (.var 0)))) (.again afterReply (by decide)) := by
  simp only [system, Controller.system, start, controller, Fin.cases_succ, Body.toStep, Tree.interpret]
  congr 1
  funext i
  exact i.elim0

private theorem stepAfterReply :
    system.step (extendSorts () slots) afterReply =
      .atom () (fun _ => .var 0) (.done (.straight (.tree (.var 0)))) := rfl

abbrev explicit : Mixed.Raw.Program sig sumSig () slots :=
  .sum () (fun j => j.elim0) (.straight (.tree (.var 0)))
    (.straight (.request () (fun _ => .var 0)))

private theorem explicitTyped : explicit.WellTyped sig sumSig strict :=
  ⟨fun j => j.elim0, le_rfl, trivial, le_rfl, fun _ => trivial⟩

/-- The smaller state uses index zero, the selected payload, even though
index one still refers to the original loop entry's payload. -/
example :
    Mixed.Ranked.Scoped.Step.native (ε := Fx) sig sumSig (@entryRank _ _ sig () 1 Fx _ _)
      (controller.system sig sumSig strict controllerTyped).endpoint
      ((controller.system sig sumSig strict controllerTyped).step slots start) =
    (.case (.op (.inr ()) .unit) (.bv 0)
      (.iter (.inl (.bv 0)) (controller.loopBody sig sumSig (Γ.length + 1)))) :=
  rfl

private theorem expansion_eq :
    controller.expansion sig sumSig strict controllerTyped start = explicit.compile sig sumSig (ε := Fx) := by
  unfold Controller.expansion
  rw [Mixed.Ranked.Scoped.System.expand_step, stepStart]
  simp only [Mixed.Ranked.Scoped.Step.expand, Mixed.Raw.Program.compile, Flatten.compile, Mixed.ofSequence]
  rw [Mixed.Ranked.Scoped.System.expand_step, stepAfterReply]
  simp [Mixed.Ranked.Scoped.Step.expand, Mixed.Raw.Program.compile, Flatten.compile, Flatten.emit,
    Mixed.ofSequence, visible]

example : ∃ t : Tm Empty (Unit ⊕ Unit) Γ.length, explicit.source.toLetIter Γ.length = some t ∧
    HasTypeEffect free Γ.toBoundCtx (controller.loop sig sumSig start) A strict ∧
    AbortEquiv (⊥ : Fx) free Γ.toBoundCtx (controller.loop sig sumSig start) t A ∧
    Eqv Γ A strict (controller.expansion sig sumSig strict controllerTyped start).source explicit.source := by
  have hΓ : Γ.Pure := fun i => Fin.cases rfl (fun j => j.elim0) i
  have hs : ∀ i : Fin Γ.length, (Γ.get i).1 = .base (slots i) :=
    fun i => Fin.cases rfl (fun j => j.elim0) i
  have he : IsIterative strict := rfl
  obtain ⟨t, ht, _⟩ := (Mixed.Raw.source_wf sig sumSig hΓ hs strict explicit explicitTyped).toLetIter
  have h := raw_endpoint_reflection sig sumSig visible strict he controller controllerTyped
    hΓ hs start explicit explicitTyped ht
  have heq : Eqv Γ A strict (controller.expansion sig sumSig strict controllerTyped start).source explicit.source := by
    rw [expansion_eq]
    exact (Mixed.Raw.compile_eqv sig sumSig hΓ hs strict explicit explicitTyped).symm
  exact ⟨t, ht, (controller.checked sig sumSig strict he controllerTyped).endpoint_typed hΓ hs start,
    h.mpr heq, h.mp (h.mpr heq)⟩

end LetIterCompiledRankedFixture

namespace LetIterCyclicFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response
open LetIterRankedFixture

local instance : HasEff Empty Fx := ⟨Empty.elim⟩
local instance : HasEff Unit Fx := ⟨fun _ => strict⟩
local instance : HasEff (Empty ⊕ Unit) Fx := SumCall.effects
local instance : HasTy (Empty ⊕ Unit) (Ty Unit) := SumCall.endpoints sig sumSig
local instance : EffectIteration Fx := EffectIteration.complete Fx

abbrev cycle : Term Γ.length := Mixed.repeatOnRight () Γ.length

private theorem cycleTyped : HasTypeEffect free Γ.toBoundCtx cycle A strict :=
  Mixed.repeatOnRight_typed sig sumSig rfl strict le_rfl rfl

/-- The candidate makes the same first request and returns on either reply.
The loop can repeat on the right at the same strict effect bound. -/
example :
    ∃ t : Term Γ.length, (returnEither (ss := slots)).source.toLetIter Γ.length = some t ∧
      HasTypeEffect free Γ.toBoundCtx cycle A strict ∧ HasTypeEffect free Γ.toBoundCtx t A strict ∧
      ¬ AbortEquiv (⊥ : Fx) free Γ.toBoundCtx cycle t A := by
  have hΓ : Γ.Pure := fun i => i.elim0
  have hs : ∀ i, (Γ.get i).1 = .base (slots i) := fun i => i.elim0
  let p := returnEither (ss := slots)
  have hp : p.WellTyped sig sumSig strict := ⟨fun i => i.elim0, le_rfl, trivial, trivial⟩
  obtain ⟨t, ht, htyped⟩ := (Mixed.Raw.source_wf sig sumSig hΓ hs strict p hp).toLetIter
  exact ⟨t, ht, cycleTyped, htyped, Mixed.repeatOnRight_not_raw sig sumSig rfl sumVisible hΓ hs strict p hp ht⟩

example : (returnEither (ss := slots)).visibleDepth (ε := Fx) = 1 := rfl

/-- A written product binder under an effectful case needs no raw mixed
representation to use the general written-language bound. -/
abbrev withProductBinder : Expr (Empty ⊕ Unit) :=
  .case (.op (.inr ()) .unit) (.let₂ (.pair (.var 0) (.var 0)) (.var 0)) (.var 0)

private theorem productBinderTyped : Wf Γ withProductBinder A strict :=
  .case (A := A) (B := A) (.op (f := Sum.inr ()) le_rfl (.unit _ _))
    (.let₂ (.pair (.var 0 bot_le) (.var 0 bot_le)) (.var 0 bot_le))
    (.var 0 bot_le)

example : ∃ t : Term Γ.length, withProductBinder.toLetIter Γ.length = some t ∧
    ¬ AbortEquiv (⊥ : Fx) free Γ.toBoundCtx cycle t A := by
  have hs : ∀ i, (Γ.get i).1 = .base (slots i) := fun i => i.elim0
  obtain ⟨t, ht, _⟩ := productBinderTyped.toLetIter
  exact ⟨t, ht, Mixed.repeatOnRight_not_written sig sumSig rfl sumVisible hs strict withProductBinder
    productBinderTyped ht⟩

abbrev modelSlots : Fin 1 → Unit := fun _ => ()

/-- The reply supplied by the free-tree valuation can be reused any finite
number of times along the right branch. -/
example : ∃ d : Derivation (Empty ⊕ Unit) free Γ.toBoundCtx cycle A,
    ∀ k, ITree.HasVisiblePrefix k
      (d.denote (Ty.denote (Atom sig modelSlots)) (SumCall.instructions (ε := Fx) sig sumSig modelSlots)
        (fun x => x.elim) (fun i => i.elim0)) :=
  Mixed.repeatOnRight_hasVisiblePrefixes sig sumSig rfl modelSlots (fun i => i.elim0) (.var 0)

end LetIterCyclicFixture

namespace LetIterWrittenMixedFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response

abbrev Fx := Bool × Bool
abbrev strict : Fx := (true, false)
abbrev sig : Signature Unit Bool := ⟨fun _ => 1, fun _ _ => (), fun _ => ()⟩
abbrev sumSig : SumCall.SumSignature Unit Unit :=
  ⟨fun _ => 0, fun _ i => i.elim0, fun _ => (), fun _ => ()⟩
abbrev A : Ty Unit := .base ()
abbrev Γ : EffectCtx (Ty Unit) Fx := []
abbrev free := (Ctx.nil : Ctx Empty (Ty Unit))
abbrev slots : Fin Γ.length → Unit := Fin.elim0
abbrev Ops := Bool ⊕ Unit

local instance : HasEff Bool Fx := ⟨fun _ => strict⟩
local instance : HasEff Unit Fx := ⟨fun _ => strict⟩
local instance : HasEff Ops Fx := SumCall.effects
local instance : HasTy Ops (Ty Unit) := SumCall.endpoints sig sumSig
local instance : EffectIteration Fx := EffectIteration.complete Fx

private theorem visibleAtom (f : Bool) : ¬ IsPure (⊥ : Fx) f := by
  change strict ≠ (⊥ : Fx)
  decide

private theorem visibleSum (g : Unit) : ¬ IsPure (⊥ : Fx) g := by
  change strict ≠ (⊥ : Fx)
  decide

abbrev usePayload (tag : Bool) : Expr Ops := .op (.inl tag) (.pair (.var 0) .unit)

/-- The sum request's response survives both an ordinary let and a product
binder before the case selects which visible atomic request receives it. -/
abbrev expression : Expr Ops :=
  .let₁ (.pair (.op (.inr ()) .unit) .unit)
    (.let₂ (.var 0) (.case (.var 1) (usePayload false) (usePayload true)))

private theorem expressionTyped : Wf Γ expression A strict :=
  .let₁ (.pair (.op (f := Sum.inr ()) le_rfl (.unit _ _)) (.unit _ _))
    (.let₂ (.var 0 bot_le)
      (.case (.var 1 bot_le)
        (.op (f := Sum.inl false) le_rfl (.pair (.var 0 bot_le) (.unit _ _)))
        (.op (f := Sum.inl true) le_rfl (.pair (.var 0 bot_le) (.unit _ _)))))

abbrev native : Tm Empty Ops Γ.length :=
  .let₁ (.pair (.op (.inr ()) .unit) .unit)
    (.let₂ (.bv 0) (.case (.bv 1)
      (.op (.inl false) (.pair (.bv 0) .unit))
      (.op (.inl true) (.pair (.bv 0) .unit))))

private theorem lowers : expression.toLetIter Γ.length = some native := rfl

def derivation : Derivation Ops free Γ.toBoundCtx native A :=
  .let₁ (.pair (.op (f := Sum.inr ()) .unit) .unit)
    (.let₂ .bv (.case .bv
      (.op (f := Sum.inl false) (.pair .bv .unit))
      (.op (f := Sum.inl true) (.pair .bv .unit))))

abbrev expected : Mixed.Program sig sumSig () slots :=
  .sum () (fun i => i.elim0)
    (.atom false (fun _ => .var 0) (.ret (.var 0)))
    (.atom true (fun _ => .var 0) (.ret (.var 0)))

private theorem expectedTyped : expected.WellTyped sig sumSig strict :=
  ⟨fun i => i.elim0, le_rfl,
    ⟨fun _ => trivial, visibleAtom false, le_rfl, trivial⟩,
    ⟨fun _ => trivial, visibleAtom true, le_rfl, trivial⟩⟩

private theorem ctxPure : Γ.Pure := fun i => i.elim0
private theorem slotsTyped : ∀ i, (Γ.get i).1 = .base (slots i) := fun i => i.elim0

variable {m : Nat} (ms : Fin m → Unit)

local notation "D" => Ty.denote (Atom sig ms)
local notation "M" => SumCall.instructions (ε := Fx) sig sumSig ms
local notation "emptyEnv" => (fun x : Empty => x.elim)

private theorem evalAtom (f : Bool) (r : Atom sig ms ()) :
    (M).eval (.inl f) (r, PUnit.unit) =
      ITree.vis (.atom f (fun _ => r.down)) (fun reply => ITree.ret ⟨reply⟩) := by
  change (M).eval (.inl f) (packArgs sig ms 1 (sig.arg f) (fun _ => r.down)) = _
  simp only [SumCall.instructions, ite_eq_right (visibleAtom f), readArgs, unpackArgs_packArgs]

private theorem evalSum :
    (M).eval (.inr ()) PUnit.unit =
      ITree.vis (.sum () (fun j => j.elim0))
        (fun r => ITree.ret (SumCall.responseValue sig sumSig ms r)) := by
  change (M).eval (.inr ()) (packArgs sig ms 0 (sumSig.arg ()) (fun j => j.elim0)) = _
  simp only [SumCall.instructions, unpackArgs_packArgs]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem expressionDenote (vars : (i : Fin Γ.length) → Tree sig ms (slots i)) :
    derivation.denote D M emptyEnv (variableEnv sig ms slotsTyped vars) =
      expected.denote sig sumSig ms vars := by
  simp only [derivation, Derivation.denote, pure_bind]
  erw [evalSum ms, ITree.vis_bind, ITree.vis_bind]
  simp only [Mixed.Program.denote]
  congr 1
  · congr 1
    funext i
    exact i.elim0
  funext reply
  erw [pure_bind]
  cases reply with
  | inl r =>
    erw [pure_bind]
    exact evalAtom ms false ⟨r⟩
  | inr r =>
    erw [pure_bind]
    exact evalAtom ms true ⟨r⟩

private theorem agreesWithExpected : Eqv Γ A strict expression expected.source := by
  obtain ⟨p, hp, he⟩ := Mixed.Written.normalize_atomic sig sumSig ctxPure slotsTyped strict expressionTyped
  have eq : p = expected := by
    apply Mixed.eq_of_denote_eq sig sumSig
    intro m ms vars
    obtain ⟨dp, hdp⟩ := Mixed.eval_exists sig sumSig ms slotsTyped strict p hp
    have hn := he.toLetIter lowers (Mixed.lowers sig sumSig p)
    have agree := denote_eq_of_abortEquiv_nil.{0, 2, 0, 0} (Atom sig ms)
      (SumCall.instructions (ε := Fx) sig sumSig ms)
      (Mixed.instructions_respectsPure sig sumSig ms visibleSum) hn derivation dp
      (variableEnv sig ms slotsTyped vars)
    exact (hdp vars).symm.trans (agree.symm.trans (expressionDenote ms vars))
  exact eq ▸ he

example : AbortEquiv (⊥ : Fx) free Γ.toBoundCtx native expected.native A ∧
    Eqv Γ A strict expression expected.source := by
  have hreflect := Mixed.Written.endpoint_reflection sig sumSig visibleSum ctxPure slotsTyped strict expressionTyped
    (Mixed.source_wf sig sumSig ctxPure slotsTyped strict expected expectedTyped)
    lowers (Mixed.lowers sig sumSig expected)
  exact ⟨hreflect.mpr agreesWithExpected, hreflect.mp (hreflect.mpr agreesWithExpected)⟩

end LetIterWrittenMixedFixture

namespace LetIterStructuredResultFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response
open LetIterWrittenMixedFixture

local instance : HasEff Bool Fx := ⟨fun _ => strict⟩
local instance : HasEff Unit Fx := ⟨fun _ => strict⟩
local instance : HasEff Ops Fx := SumCall.effects
local instance : HasTy Ops (Ty Unit) := SumCall.endpoints sig sumSig
local instance : EffectIteration Fx := EffectIteration.complete Fx

abbrev Choice : Ty Unit := .coprod A A
abbrev Result : Ty Unit := .product Choice .unit
abbrev req : Expr Ops := .op (.inr ()) .unit
abbrev body : Expr Ops := .pair (.var 0) .unit
abbrev expression : Expr Ops := .let₁ req body

private theorem reqTyped : Wf Γ req Choice strict :=
  .op (f := Sum.inr ()) le_rfl (.unit _ _)

private theorem expressionTyped : Wf Γ expression Result strict :=
  .let₁ reqTyped (.pair (.var 0 bot_le) (.unit _ _))

abbrev native : Tm Empty Ops Γ.length :=
  .let₁ (.op (.inr ()) .unit) (.pair (.bv 0) .unit)

private theorem lowers : expression.toLetIter Γ.length = some native := rfl

/-- Both branches return a product with the response sum still tagged. -/
abbrev expected : Mixed.Written.Code sig sumSig Result slots :=
  .sum () (fun i => i.elim0)
    (.ret (.pair (.inl (.tree (.var 0))) .unit))
    (.ret (.pair (.inr (.tree (.var 0))) .unit))

abbrev swappedLeft : Mixed.Written.Code sig sumSig Result slots :=
  .sum () (fun i => i.elim0)
    (.ret (.pair (.inr (.tree (.var 0))) .unit))
    (.ret (.pair (.inr (.tree (.var 0))) .unit))

private theorem expectedTyped : expected.WellTyped sig sumSig strict :=
  ⟨fun i => i.elim0, le_rfl, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

private theorem swappedTyped : swappedLeft.WellTyped sig sumSig strict :=
  ⟨fun i => i.elim0, le_rfl, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

private theorem agrees : Eqv Γ Result strict expression expected.source := by
  have hL : Wf [(A, ⊥)] (.inl (.var 0) : Expr Ops) Choice (⊥ : Fx) := .inl (.var 0 le_rfl)
  have hR : Wf [(A, ⊥)] (.inr (.var 0) : Expr Ops) Choice (⊥ : Fx) := .inr (.var 0 le_rfl)
  have hl := hL.weakenEffect (bot_le : (⊥ : Fx) ≤ strict)
  have hr := hR.weakenEffect (bot_le : (⊥ : Fx) ≤ strict)
  have hc := Wf.case reqTyped hl hr
  have hb : Wf [(Choice, ⊥)] body Result strict := .pair (.var 0 bot_le) (.unit _ _)
  have hw : Wf [(Choice, ⊥), (A, ⊥)] body.wk1 Result strict := .pair (.var 0 bot_le) (.unit _ _)
  have eta := (Eqv.step (Step.rewrite hc reqTyped (.case_eta _))).symm
  have push := Eqv.step (Step.rewrite (.let₁ hc hb)
    (.case reqTyped (.let₁ hl hw) (.let₁ hr hw)) (.let1_case _ _ _ _))
  exact (Eqv.let1 eta (.refl hb)).trans
    (push.trans (.case (.refl reqTyped) (.step (.let1_beta hL hw)) (.step (.let1_beta hR hw))))

/-- Run the public reflection theorem at the original strict bound instead
of identifying the compound result with an atomic code. -/
example : AbortEquiv (⊥ : Fx) free Γ.toBoundCtx native expected.native Result ∧
    Eqv Γ Result strict expression expected.source := by
  have h := Mixed.Written.endpoint_reflection_structured sig sumSig visibleSum ctxPure slotsTyped strict
    expressionTyped agrees.endpoints_wf.2 lowers (Mixed.Written.Code.lowers sig sumSig expected)
  exact ⟨h.mpr agrees, h.mp (h.mpr agrees)⟩

/-- The very same requests with a changed injection inside the returned
product are distinguishable at their original bound. -/
example : ¬ Eqv Γ Result strict expected.source swappedLeft.source := by
  intro h
  have hn := h.toLetIter (Mixed.Written.Code.lowers sig sumSig expected)
    (Mixed.Written.Code.lowers sig sumSig swappedLeft)
  have hcode := Mixed.Written.Code.native_eq_implies_eq sig sumSig visibleSum slotsTyped strict
    expected swappedLeft expectedTyped swappedTyped hn
  simp [expected, swappedLeft] at hcode

abbrev requestThenUnit : Mixed.Written.Code sig sumSig .unit slots :=
  .sum () (fun i => i.elim0) (.ret .unit) (.ret .unit)

abbrev returnUnit : Mixed.Written.Code sig sumSig .unit slots := .ret .unit

/-- Unit compares equal at a pure return. It does not erase the preceding request. -/
example : ¬ AbortEquiv (⊥ : Fx) free Γ.toBoundCtx requestThenUnit.native returnUnit.native .unit := by
  intro h
  have hcode := Mixed.Written.Code.native_eq_implies_eq sig sumSig visibleSum slotsTyped strict
    requestThenUnit returnUnit ⟨fun i => i.elim0, le_rfl, trivial, trivial⟩ trivial h
  cases hcode

end LetIterStructuredResultFixture

namespace LetIterStructuredInputFixture

open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response
open LetIterWrittenMixedFixture (Fx strict sig sumSig A Ops free visibleSum)

local instance : HasEff Bool Fx := ⟨fun _ => strict⟩
local instance : HasEff Unit Fx := ⟨fun _ => strict⟩
local instance : HasEff Ops Fx := SumCall.effects
local instance : HasTy Ops (Ty Unit) := SumCall.endpoints sig sumSig
local instance : EffectIteration Fx := EffectIteration.complete Fx

abbrev Choice : Ty Unit := .coprod A A
abbrev Held : Ty Unit := .product Choice .unit
abbrev Γ : EffectCtx (Ty Unit) Fx := [(A, ⊥), (Held, ⊥)]

private theorem ctxPure : Γ.Pure := by
  intro i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => k.elim0) j) i

abbrev direct : Expr Ops := .case (.op (.inr ()) .unit) (.var 2) (.var 2)
abbrev rebuiltArm : Expr Ops := .let₂ (.var 2) (.pair (.var 1) (.var 0))
abbrev rebuilt : Expr Ops := .case (.op (.inr ()) .unit) rebuiltArm rebuiltArm

private theorem requestTyped : Wf Γ (.op (Sum.inr ()) .unit : Expr Ops) Choice strict :=
  .op (f := Sum.inr ()) le_rfl (.unit _ _)

private theorem directTyped : Wf Γ direct Held strict :=
  .case (A := A) (B := A) requestTyped (.var 2 bot_le) (.var 2 bot_le)

private theorem rebuiltTyped : Wf Γ rebuilt Held strict := by
  have arm : Wf ((A, ⊥) :: Γ) rebuiltArm Held strict :=
    .let₂ (.var 2 bot_le) (.pair (.var 1 bot_le) (.var 0 bot_le))
  exact .case (A := A) (B := A) requestTyped arm arm

abbrev directNative : Tm Empty Ops Γ.length :=
  .case (.op (.inr ()) .unit) (.bv 2) (.bv 2)
abbrev rebuiltNativeArm : Tm Empty Ops (Γ.length + 1) :=
  .let₂ (.bv 2) (.pair (.bv 1) (.bv 0))
abbrev rebuiltNative : Tm Empty Ops Γ.length :=
  .case (.op (.inr ()) .unit) rebuiltNativeArm rebuiltNativeArm

/-- The case performs a visible request and preserves a non-head input
product containing a sum. Native pair eta rebuilds the product in both arms. -/
example : Eqv Γ Held strict direct rebuilt := by
  have request : HasType Ops free Γ.toBoundCtx (.op (Sum.inr ()) .unit) Choice :=
    .op (f := Sum.inr ()) .unit
  have retained : HasType Ops free (.snoc Γ.toBoundCtx A) (.bv 2) Held := .bv
  have eta := Silmaril.Isotope.LetIter.LocallyNameless.Equiv.pairEta (pureEff := (⊥ : Fx)) retained
  have hn : AbortEquiv (⊥ : Fx) free Γ.toBoundCtx directNative rebuiltNative Held :=
    .equiv (.case (.refl request) eta.symm eta.symm)
  exact (Mixed.Written.endpoint_reflection_all_contexts sig sumSig visibleSum ctxPure strict
    directTyped rebuiltTyped rfl rfl).mp hn

end LetIterStructuredInputFixture
