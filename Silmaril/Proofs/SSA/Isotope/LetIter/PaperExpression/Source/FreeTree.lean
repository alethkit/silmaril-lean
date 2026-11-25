module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Defs

/-! # Free-tree interpretation and source separation -/

open Silmaril Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.Semantics.Categorical (denote_eq_of_abortEquiv_nil)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Proofs

universe u r

variable {α : Type u} {Φ : Type u} (S : Signature α Φ)

variable {n : Nat} {sorts : Fin n → α}

theorem arguments_tuple (F : α → Type (u + 1)) (k : Nat) (as : Fin k → α)
    (xs : (i : Fin k) → F (as i)) : arguments F k as (tuple F k as xs) = xs := by
  induction k with
  | zero => funext i; exact i.elim0
  | succ k ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih _ _) j

public theorem tree_free (F : α → Type (u + 1))
    (ops : (f : Φ) → ((i : Fin (S.arity f)) → F (S.arg f i)) → F (S.out f))
    (vars : (i : Fin n) → F (sorts i)) :
    ∃! g : (a : α) → Tree S sorts a → F a,
      (∀ i, g (sorts i) (.var i) = vars i) ∧
      ∀ f (xs : (i : Fin (S.arity f)) → Tree S sorts (S.arg f i)),
        g (S.out f) (.op f xs) = ops f (fun i => g (S.arg f i) (xs i)) := by
  refine ⟨fun _ t => t.interpret S F ops vars, ⟨fun _ => rfl, fun _ _ => rfl⟩, ?_⟩
  intro g hg
  funext a t
  induction t with
  | var i => exact hg.1 i
  | op f xs ih =>
    rw [hg.2]
    exact congrArg (ops f) (funext ih)

theorem tuple_lowers {k : Nat} {xs : Fin k → Expr Φ} {ys : Fin k → Tm Empty Φ n}
    (h : ∀ i, (xs i).toLetIter n = some (ys i)) :
    (sourceTuple k xs).toLetIter n = some (nativeTuple k ys) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [sourceTuple, nativeTuple, Expr.toLetIter, h 0, ih (fun i => h i.succ)]

public theorem tree_lowers {a : α} (t : Tree S sorts a) :
    t.source.toLetIter n = some t.native := by
  induction t with
  | var i => simp [Tree.source, Tree.native, Expr.toLetIter, i.isLt]
  | op f xs ih => simp [Tree.source, Tree.native, Expr.toLetIter, tuple_lowers ih]


section Typed

variable {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε]
variable {Γ : EffectCtx (Ty α) ε} {sorts : Fin Γ.length → α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "β" => Γ.toBoundCtx
local notation "D" => Ty.denote (Tree S sorts)

theorem sourceTuple_wf {k : Nat} {as : Fin k → α} {xs : Fin k → Expr Φ} {e : ε}
    (h : ∀ i, @Wf _ _ _ _ S.endpoints _ _ _ Γ (xs i) (.base (as i)) e) :
    @Wf _ _ _ _ S.endpoints _ _ _ Γ (sourceTuple k xs) (input k as) e := by
  let instr := S.endpoints
  induction k with
  | zero => exact .unit _ _
  | succ k ih => exact .pair (h 0) (ih fun i => h i.succ)

theorem tree_wf {a : α} (t : Tree S sorts a) (hp : DeclaredPure (ε := ε) S t)
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (sorts i)) (e : ε) :
    @Wf _ _ _ _ S.endpoints _ _ _ Γ t.source (.base a) e := by
  let instr := S.endpoints
  induction t with
  | var i =>
    change Wf Γ (.var i.val) (.base (sorts i)) e
    rw [← hs i]
    exact .var i (by rw [hΓ i]; exact bot_le)
  | op f xs ih =>
    exact .op (f := f) (by rw [hp.1]; exact bot_le)
      (sourceTuple_wf S (fun i => ih i (hp.2 i)))

def tupleDeriv {k : Nat} {as : Fin k → α} {xs : Fin k → Tm Empty Φ Γ.length}
    (ds : ∀ i, @Derivation _ _ _ _ _ S.endpoints Γ₀ Γ.length β (xs i) (.base (as i))) :
    @Derivation _ _ _ _ _ S.endpoints Γ₀ Γ.length β (nativeTuple k xs) (input k as) := by
  let instr := S.endpoints
  induction k with
  | zero => exact .unit
  | succ k ih => exact .pair (ds 0) (ih fun i => ds i.succ)

noncomputable def treeDerivation {a : α} (t : Tree S sorts a)
    (hs : ∀ i, (Γ.get i).1 = .base (sorts i)) :
    @Derivation _ _ _ _ _ S.endpoints Γ₀ Γ.length β t.native (.base a) := by
  let instr := S.endpoints
  induction t with
  | var i =>
    have he := (EffectCtx.get_toBoundCtx Γ i).trans (hs i)
    exact he ▸ Derivation.bv
  | op f xs ih => exact .op (f := f) (tupleDeriv S ih)

public theorem instructions_pure (observe : ObserveInput (sorts := sorts) S) :
    letI := S.endpoints
    InstructionModel.RespectsPure (ε := ε) (instructions (ε := ε) S observe) := by
  let instr := S.endpoints
  intro f hf
  exact ⟨fun x => .op f (arguments _ _ _ x), fun x => by
    simp [instructions, IsPure, hf]
    rfl⟩

def values (hs : ∀ i, (Γ.get i).1 = .base (sorts i)) : BoundEnv D β :=
  fun i => ((EffectCtx.get_toBoundCtx Γ i).trans (hs i)).symm ▸ Tree.var i

abbrev eliminateFree : FreeEnv D Γ₀ := fun x => x.elim

theorem tupleDeriv_eval (observe : ObserveInput (sorts := sorts) S) {k : Nat} {as : Fin k → α} {xs : Fin k → Tm Empty Φ Γ.length}
    (ds : ∀ i, @Derivation _ _ _ _ _ S.endpoints Γ₀ Γ.length β (xs i) (.base (as i)))
    (hs : ∀ i, (Γ.get i).1 = .base (sorts i)) (ts : (i : Fin k) → Tree S sorts (as i))
    (he : letI := S.endpoints; ∀ i, (ds i).denote D (instructions (ε := ε) S observe) (eliminateFree S) (values S hs) =
      ITree.ret (ts i)) :
    letI := S.endpoints
    (tupleDeriv S ds).denote D (instructions (ε := ε) S observe) (eliminateFree S) (values S hs) =
      ITree.ret (tuple (Tree S sorts) k as ts) := by
  let instr := S.endpoints
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((ds 0).denote D (instructions (ε := ε) S observe) (eliminateFree S) (values S hs) >>=
      (fun x => (tupleDeriv S (fun i => ds i.succ)).denote D (instructions (ε := ε) S observe)
        (eliminateFree S) (values S hs) >>= (fun y => ITree.ret (x, y)))) =
      ITree.ret (ts 0, tuple (Tree S sorts) k (fun i => as i.succ) (fun i => ts i.succ))
    rw [he 0, ih _ _ (fun i => he i.succ)]
    erw [pure_bind]
    erw [pure_bind]
    rfl

omit [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] in
theorem denote_bv_of_cast {i : Fin Γ.length} {A : Ty α}
    (e : Γ.toBoundCtx.get i = A)
    (M : @InstructionModel (Ty α) D Φ (ITree.Tree (Event Φ)) S.endpoints)
    (γ : FreeEnv D Γ₀) (ρ : BoundEnv D β) (x : D A)
    (h : ρ i = e.symm ▸ x) :
    letI := S.endpoints
    Derivation.denote D M (e ▸ Derivation.bv (ι := i)) γ ρ = ITree.ret x := by
  let instr := S.endpoints
  cases e
  exact congrArg ITree.ret h

theorem tree_eval_returns {a : α} (t : Tree S sorts a) (observe : ObserveInput (sorts := sorts) S) (hp : DeclaredPure (ε := ε) S t)
    (hs : ∀ i, (Γ.get i).1 = .base (sorts i)) :
    letI := S.endpoints
    (treeDerivation S t hs).denote D (instructions (ε := ε) S observe) (eliminateFree S) (values S hs) =
      ITree.ret t := by
  classical
  let instr := S.endpoints
  induction t with
  | var i =>
    change (Derivation.denote D (instructions (ε := ε) S observe)
      (((EffectCtx.get_toBoundCtx Γ i).trans (hs i)) ▸ Derivation.bv)
      (eliminateFree S) (values S hs)) = _
    exact denote_bv_of_cast S (sorts := sorts) (A := .base (sorts i)) _ _ _ _ (Tree.var i) rfl
  | op f xs ih =>
    change ((tupleDeriv S (fun i => treeDerivation S (xs i) hs)).denote D (instructions (ε := ε) S observe)
      (eliminateFree S) (values S hs) >>= (instructions (ε := ε) S observe).eval f) = _
    rw [tupleDeriv_eval S observe _ hs xs (fun i => ih i (hp.2 i))]
    erw [pure_bind]
    change (if IsPure (⊥ : ε) f then
      ITree.ret (Tree.op f (arguments (Tree S sorts) (S.arity f) (S.arg f)
        (tuple (Tree S sorts) (S.arity f) (S.arg f) xs)))
      else ITree.vis (Event.stop f (observe f (tuple (Tree S sorts) (S.arity f) (S.arg f) xs))) (fun z : PEmpty => z.elim)) = ITree.ret (Tree.op f xs)
    rw [ite_eq_left hp.1, arguments_tuple]

theorem tree_eval_stop {f : Φ}
    (xs : (i : Fin (S.arity f)) → Tree S sorts (S.arg f i))
    (observe : ObserveInput (sorts := sorts) S)
    (hp : ∀ i, DeclaredPure (ε := ε) S (xs i)) (hf : ¬ IsPure (⊥ : ε) f)
    (hs : ∀ i, (Γ.get i).1 = .base (sorts i)) :
    letI := S.endpoints
    (treeDerivation S (Tree.op f xs) hs).denote D (instructions (ε := ε) S observe)
      (eliminateFree S) (values S hs) =
      ITree.vis (Event.stop f (observe f (tuple (Tree S sorts) (S.arity f) (S.arg f) xs)))
        (fun z : PEmpty => z.elim) := by
  classical
  let instr := S.endpoints
  change ((tupleDeriv S (fun i => treeDerivation S (xs i) hs)).denote D (instructions (ε := ε) S observe)
    (eliminateFree S) (values S hs) >>= (instructions (ε := ε) S observe).eval f) = _
  rw [tupleDeriv_eval S observe _ hs xs (fun i => tree_eval_returns S (xs i) observe (hp i) hs)]
  erw [pure_bind]
  unfold instructions
  simp [hf]
  rfl

def eventBit {A X : Type (u + 1)} : ITree.Visible (Event Φ) A X → Option Bool
  | .ret _ => none
  | .vis (.stop _ b) _ => some b

noncomputable def firstBit {A : Type (u + 1)} (t : ITree.Tree (Event Φ) A) : _root_.Part (Option Bool) :=
  (ITree.out t).map eventBit

@[simp] theorem firstBit_stop {A : Type (u + 1)} (f : Φ) (b : Bool)
    (k : PEmpty → ITree.Tree (Event Φ) A) :
    firstBit (ITree.vis (Event.stop f b) k) = .some (some b) := by
  simp [firstBit, eventBit]

omit [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] in
theorem tuple_injective {f : Φ} :
    Function.Injective (tuple (Tree S sorts) (S.arity f) (S.arg f)) := by
  intro xs ys h
  have he := congrArg (arguments (Tree S sorts) (S.arity f) (S.arg f)) h
  simpa only [arguments_tuple] using he

/-- A label-only observation collapses calls to the same symbol even when the
pure argument tuples differ. An observation of the input can separate them. -/
theorem visible_inputs_matter {f : Φ}
    (xs ys : (i : Fin (S.arity f)) → Tree S sorts (S.arg f i))
    (hx : ∀ i, DeclaredPure (ε := ε) S (xs i)) (hy : ∀ i, DeclaredPure (ε := ε) S (ys i))
    (hf : ¬ IsPure (⊥ : ε) f) (hne : xs ≠ ys)
    (hs : ∀ i, (Γ.get i).1 = .base (sorts i)) :
    letI := S.endpoints
    ((treeDerivation S (Tree.op f xs) hs).denote D (instructions (ε := ε) S (fun _ _ => false))
        (eliminateFree S) (values S hs) =
      (treeDerivation S (Tree.op f ys) hs).denote D (instructions (ε := ε) S (fun _ _ => false))
        (eliminateFree S) (values S hs)) ∧
    ∃ observe : ObserveInput (sorts := sorts) S,
      (treeDerivation S (Tree.op f xs) hs).denote D (instructions (ε := ε) S observe)
          (eliminateFree S) (values S hs) ≠
        (treeDerivation S (Tree.op f ys) hs).denote D (instructions (ε := ε) S observe)
          (eliminateFree S) (values S hs) := by
  classical
  let instr := S.endpoints
  constructor
  · rw [tree_eval_stop S xs _ hx hf hs, tree_eval_stop S ys _ hy hf hs]
  · let a := tuple (Tree S sorts) (S.arity f) (S.arg f) xs
    let b := tuple (Tree S sorts) (S.arity f) (S.arg f) ys
    let Argument := (g : Φ) × D (input (S.arity g) (S.arg g))
    let observe : ObserveInput (sorts := sorts) S :=
      fun g p => if (⟨g, p⟩ : Argument) = ⟨f, a⟩ then false else true
    have htag : (⟨f, b⟩ : Argument) ≠ ⟨f, a⟩ := by
      intro h
      exact hne ((tuple_injective S (eq_of_heq (Sigma.mk.inj h).2)).symm)
    refine ⟨observe, ?_⟩
    rw [tree_eval_stop S xs _ hx hf hs, tree_eval_stop S ys _ hy hf hs]
    intro h
    have he := congrArg firstBit h
    rw [firstBit_stop, firstBit_stop] at he
    change Part.some (some (observe f a)) = Part.some (some (observe f b)) at he
    have hbit : observe f a = observe f b :=
      Option.some.inj (_root_.Part.some_inj.mp he)
    apply htag
    simp [observe] at hbit
    exact congrArg (fun p => (⟨f, p⟩ : Argument)) hbit

variable [DecidableEq α] [EffectIteration ε]

/-- Arbitrarily many sorts and finitary bottom-effect symbols are allowed.
The original bound is kept in the source equation, while the native purity
parameter is bottom. The native proof may use all well-typed intermediates. -/
public theorem endpoint_conservativity {a : α} (t s : Tree S sorts a)
    (ht : DeclaredPure (ε := ε) S t) (hs : DeclaredPure (ε := ε) S s)
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (sorts i)) (e : ε) :
    letI := S.endpoints
    (AbortEquiv (⊥ : ε) Γ₀ β t.native s.native (.base a) ↔
      Eqv Γ (.base a) e t.source s.source) := by
  let instr := S.endpoints
  constructor
  · intro h
    have he := denote_eq_of_abortEquiv_nil.{u, u+1, u, r} (Tree S sorts) (instructions (ε := ε) S (fun _ _ => false))
      (instructions_pure S (fun _ _ => false)) h (treeDerivation S t hslots) (treeDerivation S s hslots) (values S hslots)
    have hret : ITree.ret (E := Event Φ) t = ITree.ret s :=
      (tree_eval_returns S t (fun _ _ => false) ht hslots).symm.trans (he.trans (tree_eval_returns S s (fun _ _ => false) hs hslots))
    obtain rfl := ITree.ret_inj.mp hret
    exact .refl (tree_wf S t ht hΓ hslots e)
  · intro h
    exact h.toLetIter (tree_lowers S t) (tree_lowers S s)

/-- For these pure source endpoints the original-bound Eqv identifies
exactly the identical free trees. -/
public theorem source_eqv_iff {a : α} (t s : Tree S sorts a)
    (ht : DeclaredPure (ε := ε) S t) (hs : DeclaredPure (ε := ε) S s)
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (sorts i)) (e : ε) :
    letI := S.endpoints
    (Eqv Γ (.base a) e t.source s.source ↔ t = s) := by
  let instr := S.endpoints
  constructor
  · intro h
    have hn := h.toLetIter (tree_lowers S t) (tree_lowers S s)
    have he := denote_eq_of_abortEquiv_nil.{u, u+1, u, r} (Tree S sorts) (instructions (ε := ε) S (fun _ _ => false))
      (instructions_pure S (fun _ _ => false)) hn (treeDerivation S t hslots) (treeDerivation S s hslots) (values S hslots)
    exact ITree.ret_inj.mp ((tree_eval_returns S t (fun _ _ => false) ht hslots).symm.trans (he.trans (tree_eval_returns S s (fun _ _ => false) hs hslots)))
  · rintro rfl
    exact .refl (tree_wf S t ht hΓ hslots e)


/-- Inequality holds in the full fixed-bound source relation, for calls
which are well typed at that bound. -/
public theorem effectful_call_source_inequality {f : Φ}
    (xs ys : (i : Fin (S.arity f)) → Tree S sorts (S.arg f i))
    (hx : ∀ i, DeclaredPure (ε := ε) S (xs i)) (hy : ∀ i, DeclaredPure (ε := ε) S (ys i))
    (hf : ¬ IsPure (⊥ : ε) f) (hne : xs ≠ ys)
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (sorts i)) {e : ε}
    (hle : instrEff f ≤ e) :
    letI := S.endpoints
    let x := Tree.op f xs
    let y := Tree.op f ys
    Wf Γ x.source (.base (S.out f)) e ∧ Wf Γ y.source (.base (S.out f)) e ∧
      ¬ Eqv Γ (.base (S.out f)) e x.source y.source := by
  let instr := S.endpoints
  refine ⟨.op hle (sourceTuple_wf S (fun i => tree_wf S (xs i) (hx i) hΓ hslots e)),
    .op hle (sourceTuple_wf S (fun i => tree_wf S (ys i) (hy i) hΓ hslots e)), ?_⟩
  intro he
  let x := Tree.op f xs
  let y := Tree.op f ys
  obtain ⟨observe, hsep⟩ := (visible_inputs_matter S xs ys hx hy hf hne hslots).2
  have h := he.toLetIter (tree_lowers S x) (tree_lowers S y)
  exact hsep (denote_eq_of_abortEquiv_nil.{u, u+1, u, r} (Tree S sorts)
    (instructions (ε := ε) S observe) (instructions_pure S observe) h
    (treeDerivation S x hslots) (treeDerivation S y hslots) (values S hslots))

end Typed

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Proofs
