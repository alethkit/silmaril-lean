module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Thms

/-! # Separation at a fresh response for a single call -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.Semantics Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SingleCall.Proofs

universe u r

variable {α Φ : Type u} (S : Signature α Φ) {ε : Type r} [HasEff Φ ε]

section Evaluation

variable {n : Nat} (modelSlots : Fin n → α)
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

local notation "D" => Ty.denote (Atom S modelSlots)
local notation "β" => Γ.toBoundCtx
local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

private def tupleDerivation {m : Nat} {as : Fin m → α} {ts : Fin m → Tm Empty Φ Γ.length}
    (ds : ∀ i, @Derivation _ _ _ _ _ S.endpoints Γ₀ Γ.length β (ts i) (.base (as i))) :
    @Derivation _ _ _ _ _ S.endpoints Γ₀ Γ.length β (nativeTuple m ts) (input m as) := by
  let instr := S.endpoints
  induction m with
  | zero => exact .unit
  | succ m ih => exact .pair (ds 0) (ih fun i => ds i.succ)

private noncomputable def treeDerivation {c : α} (p : Tree S slots c)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) :
    @Derivation _ _ _ _ _ S.endpoints Γ₀ Γ.length β p.native (.base c) := by
  let instr := S.endpoints
  induction p with
  | var i =>
    have hi := (EffectCtx.get_toBoundCtx Γ i).trans (hslots i)
    exact hi ▸ Derivation.bv
  | op f xs ih => exact .op (f := f) (tupleDerivation S ih)

private def env (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (vars : (i : Fin Γ.length) → Tree S modelSlots (slots i)) : BoundEnv D β :=
  fun i => ((EffectCtx.get_toBoundCtx Γ i).trans (hslots i)).symm ▸ (⟨vars i⟩ : Atom S modelSlots _)

private def freeEnv : FreeEnv D Γ₀ := fun x => x.elim

omit [HasEff Φ ε] in
private theorem eval_cast_bv {i : Fin Γ.length} {A : Ty α}
    (e : (β).get i = A) (M : @InstructionModel (Ty α) D Φ (ITree.Tree (Event S modelSlots)) S.endpoints)
    (ρ : BoundEnv D β) (x : D A) (h : ρ i = e.symm ▸ x) :
    letI := S.endpoints
    Derivation.denote D M (e ▸ Derivation.bv (ι := i)) (freeEnv S modelSlots) ρ = ITree.ret x := by
  let instr := S.endpoints
  cases e
  exact congrArg ITree.ret h

variable [Bot ε]

local notation "M" => instructions (ε := ε) S modelSlots

private theorem eval_tuple (ρ : BoundEnv D β) {m : Nat} {as : Fin m → α}
    {ts : Fin m → Tm Empty Φ Γ.length}
    (ds : ∀ i, @Derivation _ _ _ _ _ S.endpoints Γ₀ Γ.length β (ts i) (.base (as i)))
    (xs : (i : Fin m) → Tree S modelSlots (as i))
    (he : letI := S.endpoints
      ∀ i, (ds i).denote D M (freeEnv S modelSlots) ρ = ITree.ret ⟨xs i⟩) :
    letI := S.endpoints
    (tupleDerivation S ds).denote D M (freeEnv S modelSlots) ρ =
      ITree.ret (packArgs S modelSlots m as xs) := by
  let instr := S.endpoints
  induction m with
  | zero => rfl
  | succ m ih =>
    change ((ds 0).denote D M (freeEnv S modelSlots) ρ >>= fun x =>
      (tupleDerivation S (fun i => ds i.succ)).denote D M (freeEnv S modelSlots) ρ >>= fun y =>
        ITree.ret (x, y)) = _
    rw [he 0, ih (fun i => ds i.succ) (fun i => xs i.succ) (fun i => he i.succ)]
    erw [pure_bind]
    erw [pure_bind]
    rfl

private theorem eval_tree {c : α} (p : Tree S slots c) (hp : DeclaredPure (ε := ε) S p)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (vars : (i : Fin Γ.length) → Tree S modelSlots (slots i)) :
    letI := S.endpoints
    (treeDerivation S p hslots).denote D M (freeEnv S modelSlots) (env S modelSlots hslots vars) =
      ITree.ret ⟨p.interpret S (Tree S modelSlots) Tree.op vars⟩ := by
  classical
  let instr := S.endpoints
  induction p with
  | var i =>
    change (Derivation.denote D M
      (((EffectCtx.get_toBoundCtx Γ i).trans (hslots i)) ▸ Derivation.bv)
      (freeEnv S modelSlots) (env S modelSlots hslots vars)) = _
    exact eval_cast_bv S modelSlots (A := .base (slots i)) _ _ _ ⟨vars i⟩ rfl
  | op f xs ih =>
    let vs := fun i => (xs i).interpret S (Tree S modelSlots) Tree.op vars
    change ((tupleDerivation S (fun i => treeDerivation S (xs i) hslots)).denote D M
      (freeEnv S modelSlots) (env S modelSlots hslots vars) >>= (M).eval f) =
      ITree.ret ⟨.op f vs⟩
    rw [eval_tuple S modelSlots _ _ vs (fun i => ih i (hp.2 i))]
    erw [pure_bind]
    simp only [instructions, ite_eq_left hp.1, readArgs, unpackArgs_packArgs]

end Evaluation

section SingleCall

variable [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] [DecidableEq α]
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}
  {f : Φ} {c : α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "Γ⁺" => ((Ty.base (S.out f), (⊥ : ε)) :: Γ)
private abbrev responseSlots (f : Φ) {k : Nat} (ambient : Fin k → α) : Fin (k + 1) → α :=
  Fin.cases (S.out f) ambient

local notation "slots⁺" => (responseSlots S f slots)
local notation "β" => Γ.toBoundCtx

omit [HasEff Φ ε] [EffectIteration ε] [DecidableEq α] in
private theorem extendedSlots (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) :
    ∀ i : Fin (List.length Γ⁺), (List.get Γ⁺ i).1 = .base ((slots⁺) i) := by
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  exact hslots j

omit [HasEff Φ ε] [EffectIteration ε] [DecidableEq α] in
private theorem extendedPure (hΓ : Γ.Pure) : EffectCtx.Pure Γ⁺ := by
  intro i
  exact Fin.cases (motive := fun j => (List.get Γ⁺ j).2 = ⊥) rfl hΓ i

omit [HasEff Φ ε] [EffectIteration ε] [DecidableEq α] in
private theorem env_at_fresh (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) :
    BoundEnv.snoc (D := Ty.denote (Atom S slots⁺)) (A := .base (S.out f))
      (env S slots⁺ hslots (fun i => Tree.var i.succ)) ⟨Tree.var 0⟩ =
      env S slots⁺ (extendedSlots S (f := f) hslots) Tree.var := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

omit [DecidableEq α] in
private theorem interpret_vars {n : Nat} {ss : Fin n → α} {a : α} (p : Tree S ss a) :
    p.interpret S (Tree S ss) Tree.op Tree.var = p := by
  induction p with
  | var i => rfl
  | op f xs ih =>
    change Tree.op f (fun i => (xs i).interpret S (Tree S ss) Tree.op Tree.var) = _
    exact congrArg (Tree.op f) (funext ih)

omit [EffectIteration ε] [DecidableEq α] in
private theorem request_wf (args : (i : Fin (S.arity f)) → Tree S slots (S.arg f i))
    (hargs : ∀ i, DeclaredPure (ε := ε) S (args i))
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) {e : ε}
    (he : instrEff f ≤ e) :
    letI := S.endpoints
    Wf Γ (Tree.op f args).source (.base (S.out f)) e := by
  let instr := S.endpoints
  suffices h : ∀ {m : Nat} {as : Fin m → α} (xs : (i : Fin m) → Tree S slots (as i)),
      (∀ i, DeclaredPure (ε := ε) S (xs i)) →
      Wf Γ (sourceTuple m (fun i => (xs i).source)) (input m as) e from
    .op he (h args hargs)
  intro m as xs hx
  induction m with
  | zero => exact .unit _ _
  | succ m ih =>
    exact .pair (tree_wf S (xs 0) (hx 0) hΓ hslots e)
      (ih (as := fun i => as i.succ) (fun i => xs i.succ) fun i => hx i.succ)

omit [EffectIteration ε] in
private theorem normalized_continuations_eq
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (args : (i : Fin (S.arity f)) → Tree S slots (S.arg f i))
    (hargs : ∀ i, DeclaredPure (ε := ε) S (args i))
    (hf : ¬ IsPure (⊥ : ε) f)
    (p q : Tree S (slots⁺) c) (hp : DeclaredPure (ε := ε) S p) (hq : DeclaredPure (ε := ε) S q)
    (h : letI := S.endpoints
      AbortEquiv (⊥ : ε) Γ₀ β
        (.let₁ (Tree.op f args).native p.native) (.let₁ (Tree.op f args).native q.native)
        (.base c)) : p = q := by
  let instr := S.endpoints
  let ρ := env S slots⁺ hslots (fun i => Tree.var i.succ)
  let M := instructions (ε := ε) S slots⁺
  let D := Ty.denote (Atom S slots⁺)
  let ds := fun i => treeDerivation S (args i) hslots
  let hslots' := extendedSlots S (f := f) hslots
  let dp := treeDerivation S (Γ := Γ⁺) p hslots'
  let dq := treeDerivation S (Γ := Γ⁺) q hslots'
  let k (r : Atom S slots⁺ (S.out f)) := dp.denote D M (freeEnv S slots⁺) (ρ.snoc r)
  let l (r : Atom S slots⁺ (S.out f)) := dq.denote D M (freeEnv S slots⁺) (ρ.snoc r)
  have he := native_sound (ε := ε) S slots⁺
    (.let₁ (.op (tupleDerivation S ds)) dp) (.let₁ (.op (tupleDerivation S ds)) dq) ρ h
  let vs := fun i => (args i).interpret S (Tree S slots⁺) Tree.op (fun j => .var j.succ)
  change (((tupleDerivation S ds).denote D M (freeEnv S slots⁺) ρ >>= M.eval f) >>= k) =
    (((tupleDerivation S ds).denote D M (freeEnv S slots⁺) ρ >>= M.eval f) >>= l) at he
  rw [eval_tuple S slots⁺ ρ ds vs (fun i => eval_tree S slots⁺ (args i) (hargs i) hslots _)] at he
  erw [pure_bind] at he
  have hresp := (eval_bind_eq_iff S slots⁺ hf _ k l).mp he (.var 0)
  change dp.denote D M (freeEnv S slots⁺) (ρ.snoc ⟨.var 0⟩) =
    dq.denote D M (freeEnv S slots⁺) (ρ.snoc ⟨.var 0⟩) at hresp
  rw [env_at_fresh S (f := f) hslots] at hresp
  have hpv := eval_tree S slots⁺ p hp hslots' Tree.var
  have hqv := eval_tree S slots⁺ q hq hslots' Tree.var
  have hret := hpv.symm.trans (hresp.trans hqv)
  exact (interpret_vars S p).symm.trans
    ((congrArg ULift.down (ITree.ret_inj.mp hret)).trans (interpret_vars S q))

omit [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] [DecidableEq α] in
private theorem lower_call
    (args : (i : Fin (S.arity f)) → Tree S slots (S.arg f i))
    {body : Expr Φ} {bodyTm : Tm Empty Φ (Γ.length + 1)}
    (hbody : body.toLetIter (Γ.length + 1) = some bodyTm) :
    (Expr.let₁ (Tree.op f args).source body).toLetIter Γ.length =
      some (.let₁ (Tree.op f args).native bodyTm) := by
  simp only [Expr.toLetIter, tree_lowers S, hbody, Option.bind_some, Option.map_some]

public theorem continuation_eqv
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (args : (i : Fin (S.arity f)) → Tree S slots (S.arg f i))
    (hargs : ∀ i, DeclaredPure (ε := ε) S (args i))
    (hf : ¬ IsPure (⊥ : ε) f) (e : ε) (he : instrEff f ≤ e)
    {a b : Expr Φ}
    (ha : letI := S.endpoints; Wf Γ⁺ a (.base c) (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ⁺ b (.base c) (⊥ : ε))
    {t s : Tm Empty Φ (Γ.length + 1)}
    (ht : a.toLetIter (Γ.length + 1) = some t) (hs : b.toLetIter (Γ.length + 1) = some s)
    (hn : letI := S.endpoints
      AbortEquiv (⊥ : ε) Γ₀ β (.let₁ (Tree.op f args).native t)
        (.let₁ (Tree.op f args).native s) (.base c)) :
    letI := S.endpoints
    Eqv Γ⁺ (.base c) e a b := by
  let instr := S.endpoints
  have hcall := Eqv.refl (request_wf S args hargs hΓ hslots he)
  have hΓ' := extendedPure S (f := f) hΓ
  have hslots' := extendedSlots S (f := f) hslots
  obtain ⟨p, hp, eqp⟩ := Normalization.normalizesToTree S ha hΓ' hslots' e
  obtain ⟨q, hq, eqq⟩ := Normalization.normalizesToTree S hb hΓ' hslots' e
  have hl := (Eqv.let1 hcall eqp).toLetIter (lower_call S args ht) (lower_call S args (tree_lowers S p))
  have hr := (Eqv.let1 hcall eqq).toLetIter (lower_call S args hs) (lower_call S args (tree_lowers S q))
  obtain rfl := normalized_continuations_eq S hslots args hargs hf p q hp hq
    (hl.symm.trans (hn.trans hr))
  exact eqp.trans eqq.symm

public theorem endpoint_reflection
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (args : (i : Fin (S.arity f)) → Tree S slots (S.arg f i))
    (hargs : ∀ i, DeclaredPure (ε := ε) S (args i))
    (hf : ¬ IsPure (⊥ : ε) f) (e : ε) (he : instrEff f ≤ e)
    {a b : Expr Φ}
    (ha : letI := S.endpoints; Wf Γ⁺ a (.base c) (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ⁺ b (.base c) (⊥ : ε))
    {t s : Tm Empty Φ (Γ.length + 1)}
    (ht : a.toLetIter (Γ.length + 1) = some t) (hs : b.toLetIter (Γ.length + 1) = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) Γ₀ β (.let₁ (Tree.op f args).native t)
        (.let₁ (Tree.op f args).native s) (.base c) ↔
      Eqv Γ (.base c) e (.let₁ (Tree.op f args).source a) (.let₁ (Tree.op f args).source b) := by
  let instr := S.endpoints
  refine ⟨fun hn => ?_, fun h => h.toLetIter (lower_call S args ht) (lower_call S args hs)⟩
  exact Eqv.let1 (.refl (request_wf S args hargs hΓ hslots he))
    (continuation_eqv S hΓ hslots args hargs hf e he ha hb ht hs hn)


end SingleCall

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SingleCall.Proofs
