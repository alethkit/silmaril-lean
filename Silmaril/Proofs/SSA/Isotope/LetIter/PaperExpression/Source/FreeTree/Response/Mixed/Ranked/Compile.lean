module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Compile.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Thms

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall
  (SumSignature treeNative endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Compile.Proofs

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {a c : α} {k n m grade : Nat}
  {ss : Fin n → α} {target : Fin m → α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "N" => Term (Φ := Φ) (Ψ := Ψ)

private theorem tag_bsubst {t : N n} (i : Fin (k + 1)) (σ : Fin n → N m) :
    (tag i t).bsubst σ = tag i (t.bsubst σ) := by
  induction k with
  | zero => rfl
  | succ k ih => refine Fin.cases rfl (fun j => ?_) i
                 simp [tag, Tm.bsubst, ih]

private theorem dispatch_bsubst (branches : Fin (k + 1) → N 1) (t : N n) (σ : Fin n → N m) :
    (dispatch k branches t).bsubst σ = dispatch k branches (t.bsubst σ) := by
  induction k generalizing n m with
  | zero => simp [dispatch, Tm.bsubst_comp]
  | succ k ih => simp [dispatch, Tm.bsubst, Tm.bsubst_comp, ih, Tm.upSub]

private theorem tuple_bsubst (l : Nat) (ts : Fin l → N n) (σ : Fin n → N m) :
    (nativeTuple l ts).bsubst σ = nativeTuple l (fun i => (ts i).bsubst σ) := by
  induction l with
  | zero => rfl
  | succ l ih => simp [nativeTuple, Tm.bsubst, ih]

private theorem tree_bsubst (p : Tree S ss a) (σ : Sequence.TreeSubst S ss target) :
    (treeNative S p).bsubst (fun i => treeNative (Ψ := Ψ) S (σ i)) =
      treeNative S (p.interpret S _ Tree.op σ) := by
  induction p with
  | var => rfl
  | op f ts ih =>
    simp [Tree.interpret, treeNative, Tm.bsubst, tuple_bsubst, ih]

private theorem lift_tree_bsubst (σ : Sequence.TreeSubst S ss target) (x : α) :
    Tm.upSub (fun i => treeNative (Ψ := Ψ) S (σ i)) =
      fun i => treeNative S (Sequence.liftSubst S σ x i) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  change (treeNative S (σ j)).lift =
    treeNative S ((σ j).interpret S (Tree S (extendSorts x target)) Tree.op (fun j : Fin m => .var j.succ))
  have h := tree_bsubst (Ψ := Ψ) S (σ j) (target := extendSorts x target)
    (show Sequence.TreeSubst S target (extendSorts x target) from fun i => .var i.succ)
  exact (Tm.bsubst_bv_eq_rename Fin.succ _).symm.trans h

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

local notation "HT" β:arg t:arg A:arg =>
  @HasType (Ty α) _ Empty _ (Φ ⊕ Ψ) (endpoints S T) Γ₀ _ β t A
local notation "TE" β:arg t:arg A:arg e:arg =>
  @HasTypeEffect Empty (Φ ⊕ Ψ) ε _ _ _ effects _ (Ty α) _ (endpoints S T) _ Γ₀ β t A e
local notation "EQ" β:arg t:arg s:arg A:arg =>
  @LocallyNameless.Equiv (Ty α) _ Empty _ (Φ ⊕ Ψ) (endpoints S T) ε effects ⊥ Γ₀ _ β t s A
local notation "PU" t:arg => @LocallyNameless.Pure Empty (Φ ⊕ Ψ) ε effects ⊥ _ t

omit [EffectIteration ε] in
private theorem tuple_pure (l : Nat) (ts : Fin l → N n) (h : ∀ i, PU (ts i)) :
    PU (nativeTuple l ts) := by
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  induction l with
  | zero => exact .unit
  | succ l ih => exact .pair (h 0) (ih (fun i => ts i.succ) fun i => h i.succ)

omit [EffectIteration ε] in
private theorem tree_pure (p : Tree S ss a) (h : DeclaredPure (ε := ε) S p) :
    PU (treeNative S p) := by
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  induction p with
  | var => exact .bv
  | op f ts ih => exact .op h.1 (tuple_pure (S.arity f) _ (fun i => ih i (h.2 i)))

private theorem tuple_type (l : Nat) (xs : Fin l → α) {β : BoundCtx (Ty α) n}
    (ts : Fin l → N n) (h : ∀ i, HT β (ts i) (.base (xs i))) :
    HT β (nativeTuple l ts) (input l xs) := by
  let _ := endpoints S T
  induction l with
  | zero => exact .unit
  | succ l ih => exact .pair (h 0) (ih (fun i => xs i.succ) _ fun i => h i.succ)

private theorem tree_type {β : BoundCtx (Ty α) n} (hs : ∀ i, β.get i = .base (ss i))
    (p : Tree S ss a) : HT β (treeNative S p) (.base a) := by
  let _ := endpoints S T
  induction p with
  | var i => exact hs i ▸ .bv
  | op f ts ih => exact .op (tuple_type S T (S.arity f) (S.arg f) _ ih)

private theorem slots_snoc {β : BoundCtx (Ty α) n} (hs : ∀ i, β.get i = .base (ss i)) (x : α) :
    ∀ i, (β.snoc (.base x)).get i = .base (extendSorts x ss i) :=
  Fin.cases rfl hs

private theorem tag_type {β : BoundCtx (Ty α) n} {t : N n}
    (h : HT β t (.base a)) (i : Fin (k + 1)) : HT β (tag i t) (stateType a k) := by
  let _ := endpoints S T
  induction k with
  | zero => exact h
  | succ k ih => exact Fin.cases (.inl h) (fun j => .inr (ih j)) i

omit [EffectIteration ε] in
private theorem tag_pure {t : N n} (h : PU t) (i : Fin (k + 1)) : PU (tag i t) := by
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  induction k with
  | zero => exact h
  | succ k ih => exact Fin.cases (.inl h) (fun j => .inr (ih j)) i

private theorem dispatch_type {β : BoundCtx (Ty α) n} {t : N n} {C : Ty α}
    (branches : Fin (k + 1) → N 1) (hb : ∀ i, HT (.snoc .nil (.base a)) (branches i) C)
    (ht : HT β t (stateType a k)) : HT β (dispatch k branches t) C := by
  let _ := endpoints S T
  induction k generalizing n with
  | zero => exact HasType.bsubst (fun i => Fin.cases ht (fun j => j.elim0) i) (hb 0)
  | succ k ih =>
    exact .case ht (HasType.bsubst (fun i => Fin.cases .bv (fun j => j.elim0) i) (hb 0))
      (ih (fun j => branches j.succ) (fun j => hb j.succ) .bv)

private theorem dispatch_typed {β : BoundCtx (Ty α) n} {t : N n} {C : Ty α} (e : ε)
    (branches : Fin (k + 1) → N 1) (hb : ∀ i, TE (.snoc .nil (.base a)) (branches i) C e)
    (ht : HT β t (stateType a k)) (hp : PU t) : TE β (dispatch k branches t) C e := by
  let _ := endpoints S T
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  induction k generalizing n with
  | zero => exact (hb 0).bsubst_bot (fun i => Fin.cases ⟨ht, hp.hasEffect⟩ (fun j => j.elim0) i)
  | succ k ih =>
    have hl : TE (.snoc β (.base a)) ((branches 0).bsubst (fun _ => .bv 0)) C e :=
      (hb 0).bsubst_bot (fun i => Fin.cases ⟨.bv, bot_le⟩ (fun j => j.elim0) i)
    have hr := ih (β := .snoc β (stateType a k)) (t := .bv 0)
      (fun j => branches j.succ) (fun j => hb j.succ) .bv .bv
    exact ⟨.case ht hl.1 hr.1, sup_le (hp.hasEffect.mono bot_le) (sup_le hl.2 hr.2)⟩

omit [EffectIteration ε] in
private theorem dispatch_tag {β : BoundCtx (Ty α) n} {t : N n} {C : Ty α}
    (branches : Fin (k + 1) → N 1) (hb : ∀ i, HT (.snoc .nil (.base a)) (branches i) C)
    (ht : HT β t (.base a)) (hp : PU t) (i : Fin (k + 1)) :
    EQ β (dispatch k branches (tag i t)) ((branches i).bsubst (fun _ => t)) C := by
  let _ := endpoints S T
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  induction k with
  | zero =>
    have hz : i = 0 := Fin.cases rfl (fun j => j.elim0) i
    subst i
    exact .refl (HasType.bsubst (fun j => Fin.cases ht (fun j => j.elim0) j) (hb 0))
  | succ k ih =>
    let left : N (n + 1) := (branches 0).bsubst (fun _ => .bv 0)
    let right : N (n + 1) := dispatch k (fun j => branches j.succ) (.bv 0)
    have hl : HT (.snoc β (.base a)) left C :=
      HasType.bsubst (fun j => Fin.cases .bv (fun j => j.elim0) j) (hb 0)
    have hr : HT (.snoc β (stateType a k)) right C :=
      dispatch_type S T _ (fun j => hb j.succ) .bv
    refine Fin.cases (motive := fun j =>
      EQ β (dispatch (k + 1) branches (tag j t)) ((branches j).bsubst (fun _ => t)) C) ?_ ?_ i
    · have h := (Equiv.caseBetaL ht hl hr).trans (Equiv.letBeta hp ht hl)
      simpa [dispatch, tag, left, right, Tm.instantiate, Tm.bsubst_comp, Tm.bsubst] using h
    · intro j
      have htag := tag_type S T ht j
      have h := (Equiv.caseBetaR htag hl hr).trans (Equiv.letBeta (tag_pure hp j) htag hr)
      have h' := ih _ (fun j => hb j.succ) j
      have hs : right.instantiate (tag j t) = dispatch k (fun j => branches j.succ) (tag j t) := by
        simp [right, Tm.instantiate, dispatch_bsubst, Tm.bsubst]
      exact (hs ▸ h).trans h'


omit [EffectIteration ε] in
private theorem step_typed (e : ε) (b : Body S T a c k grade ss) (hb : b.WellTyped S T e)
    (σ : Sequence.TreeSubst S ss target) (hσ : ∀ i, DeclaredPure (ε := ε) S (σ i)) :
    Scoped.Step.WellTyped S T (@entryRank _ _ S a k ε _ _) e (b.toStep S T e hb σ hσ) := by
  induction b generalizing m with
  | done p => exact Sequence.tree_pure_subst S p hb σ hσ
  | again => trivial
  | atom f args next ih =>
    exact ⟨fun i => Sequence.tree_pure_subst S _ (hb.1 i) σ hσ, hb.2.1, hb.2.2.1,
      ih hb.2.2.2 _ (Body.liftSubst_pure S σ hσ _)⟩
  | sum g args left right ihl ihr =>
    exact ⟨fun i => Sequence.tree_pure_subst S _ (hb.1 i) σ hσ, hb.2.1,
      ihl hb.2.2.1 _ (Body.liftSubst_pure S σ hσ _), ihr hb.2.2.2 _ (Body.liftSubst_pure S σ hσ _)⟩

private abbrev Answer (a c : α) (k : Nat) : Ty α := .coprod (.base c) (stateType a k)

private theorem encode_typed {β : BoundCtx (Ty α) n} (hs : ∀ i, β.get i = .base (ss i))
    (e : ε) (b : Body S T a c k grade ss) (hb : b.WellTyped S T e) :
    TE β (b.encode S T) (Answer a c k) e := by
  let _ := endpoints S T
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  induction b with
  | done p => exact ⟨.inl (tree_type S T hs p), (tree_pure S p hb).hasEffect.mono bot_le⟩
  | again j hj p =>
    exact ⟨.inr (tag_type S T (tree_type S T hs p) j), (tag_pure (tree_pure S p hb) j).hasEffect.mono bot_le⟩
  | atom f args next ih =>
    have hargs := tuple_type S T (S.arity f) (S.arg f) _ (fun i => tree_type S T hs (args i))
    have hpu := tuple_pure (S.arity f) _ (fun i => tree_pure (Ψ := Ψ) S (args i) (hb.1 i))
    have hn := ih (slots_snoc hs (S.out f)) hb.2.2.2
    exact ⟨.let₁ (.op hargs) hn.1, sup_le (sup_le hb.2.2.1 (hpu.hasEffect.mono bot_le)) hn.2⟩
  | sum g args left right ihl ihr =>
    have hargs := tuple_type S T (T.arity g) (T.arg g) _ (fun i => tree_type S T hs (args i))
    have hpu := tuple_pure (T.arity g) _ (fun i => tree_pure (Ψ := Ψ) S (args i) (hb.1 i))
    have hl := ihl (slots_snoc hs (T.left g)) hb.2.2.1
    have hr := ihr (slots_snoc hs (T.right g)) hb.2.2.2
    exact ⟨.case (.op hargs) hl.1 hr.1, sup_le (sup_le hb.2.1 (hpu.hasEffect.mono bot_le)) (sup_le hl.2 hr.2)⟩

private theorem template_typed (p : Controller S T a c k) (e : ε)
    (hp : ∀ j, Body.WellTyped S T e (p j)) (j : Fin (k + 1)) :
    TE (.snoc .nil (.base a)) ((p j).encode S T) (Answer a c k) e :=
  encode_typed S T (Fin.cases rfl fun i => i.elim0) e _ (hp j)

private theorem loopBody_typed {β : BoundCtx (Ty α) n} (p : Controller S T a c k) (e : ε)
    (hp : ∀ j, Body.WellTyped S T e (p j)) :
    TE (.snoc β (stateType a k)) (p.loopBody S T n) (Answer a c k) e :=
by
  let _ := endpoints S T
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  exact dispatch_typed S T e _ (template_typed S T p e hp) .bv .bv

/-- A local continuation for one iteration step. The branch handling repeats
re-enters exactly the same dispatcher and uses the returned state. -/
private def handle (branches : Fin (k + 1) → N 1) (v : N n) : N n :=
  .case v (.bv 0) (.iter (.bv 0) (dispatch k branches (.bv 0)))

private theorem rename_dispatch (branches : Fin (k + 1) → N 1) (v : N n) (ρ : Fin n → Fin m) :
    (dispatch k branches v).rename ρ = dispatch k branches (v.rename ρ) := by
  rw [← Tm.bsubst_bv_eq_rename, dispatch_bsubst, Tm.bsubst_bv_eq_rename]

private theorem underBinder_restart (branches : Fin (k + 1) → N 1) :
    Tm.underBinder (.iter (.bv 0) (dispatch k branches (.bv 0)) : N (n + 1)) =
      (.iter (.bv 0) (dispatch k branches (.bv 0)) : N (n + 2)) := by
  simp [Tm.underBinder, Tm.rename, Tm.up, rename_dispatch]

private theorem underBinder_handle (branches : Fin (k + 1) → N 1) :
    (handle branches (.bv 0) : N (n + 1)).underBinder = (handle branches (.bv 0) : N (n + 2)) := by
  simp [handle, Tm.underBinder, Tm.rename, Tm.up, rename_dispatch]

private theorem handle_bsubst (branches : Fin (k + 1) → N 1) (v : N n) (σ : Fin n → N m) :
    (handle branches v).bsubst σ = handle branches (v.bsubst σ) := by
  simp [handle, Tm.bsubst, dispatch_bsubst, Tm.upSub]

omit [EffectIteration ε] in
private theorem handle_bind {β : BoundCtx (Ty α) n} {v : N n} (branches : Fin (k + 1) → N 1)
    (hb : ∀ j, HT (.snoc .nil (.base a)) (branches j) (Answer a c k))
    (hv : HT β v (Answer a c k)) :
    EQ β (handle branches v) (.let₁ v (handle branches (.bv 0))) (.base c) := by
  let _ := endpoints S T
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  have hleft : HT (.snoc β (.base c)) (.bv 0) (.base c) := .bv
  have h := Equiv.bindCase (pureEff := (⊥ : ε)) hv hleft
    (.iter .bv (dispatch_type S T branches hb .bv) :
      HT (.snoc β (stateType a k)) (.iter (.bv 0) (dispatch k branches (.bv 0))) (.base c))
  simpa only [handle, Tm.underBinder_bv_zero, underBinder_restart, BoundCtx.get, Fin.cases_zero] using h

omit [EffectIteration ε] in
private theorem handle_done {β : BoundCtx (Ty α) n} {v : N n} (branches : Fin (k + 1) → N 1)
    (hb : ∀ j, HT (.snoc .nil (.base a)) (branches j) (Answer a c k))
    (hv : HT β v (.base c)) (hp : PU v) :
    EQ β (handle branches (.inl v)) v (.base c) := by
  let _ := endpoints S T
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  have hh : HT (.snoc β (stateType a k)) (.iter (.bv 0) (dispatch k branches (.bv 0))) (.base c) :=
    .iter .bv (dispatch_type S T branches hb .bv)
  exact (Equiv.caseBetaL hv .bv hh).trans (Equiv.letBeta hp hv .bv)

omit [EffectIteration ε] in
private theorem handle_again {β : BoundCtx (Ty α) n} {v : N n} (branches : Fin (k + 1) → N 1)
    (hb : ∀ j, HT (.snoc .nil (.base a)) (branches j) (Answer a c k))
    (hv : HT β v (stateType a k)) (hp : PU v) :
    EQ β (handle branches (.inr v)) (.iter v (dispatch k branches (.bv 0))) (.base c) := by
  let _ := endpoints S T
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  have hh : HT (.snoc β (stateType a k)) (.iter (.bv 0) (dispatch k branches (.bv 0))) (.base c) :=
    .iter .bv (dispatch_type S T branches hb .bv)
  have h := (Equiv.caseBetaR hv (.bv (ι := 0) : HT (.snoc β (.base c)) (.bv 0) (.base c)) hh).trans
    (Equiv.letBeta hp hv hh)
  simpa [handle, Tm.instantiate, Tm.bsubst, dispatch_bsubst, Tm.upSub, BoundCtx.get] using h

omit [EffectIteration ε] in
private theorem handle_let {β : BoundCtx (Ty α) n} {v : N n} {b : N (n + 1)} {A : Ty α}
    (branches : Fin (k + 1) → N 1) (hb : ∀ j, HT (.snoc .nil (.base a)) (branches j) (Answer a c k))
    (hv : HT β v A) (ht : HT (.snoc β A) b (Answer a c k)) :
    EQ β (handle branches (.let₁ v b)) (.let₁ v (handle branches b)) (.base c) := by
  let _ := endpoints S T
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  have h := handle_bind (ε := ε) S T branches hb (HasType.let₁ hv ht)
  have hc := (handle_bind (ε := ε) S T (β := .snoc β (Answer a c k)) branches hb (.bv (ι := 0))).hasType.1
  have h' := Equiv.bindLet (pureEff := (⊥ : ε)) hv ht hc
  rw [underBinder_handle] at h'
  exact h.trans (h'.trans (.let₁ (.refl hv) (handle_bind S T branches hb ht).symm))

omit [EffectIteration ε] in
private theorem handle_case {β : BoundCtx (Ty α) n} {v : N n} {l r : N (n + 1)} {A B : Ty α}
    (branches : Fin (k + 1) → N 1) (hb : ∀ j, HT (.snoc .nil (.base a)) (branches j) (Answer a c k))
    (hv : HT β v (.coprod A B)) (hl : HT (.snoc β A) l (Answer a c k))
    (hr : HT (.snoc β B) r (Answer a c k)) :
    EQ β (handle branches (.case v l r)) (.case v (handle branches l) (handle branches r)) (.base c) := by
  let _ := endpoints S T
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  have h := handle_bind (ε := ε) S T branches hb (HasType.case hv hl hr)
  have hc := (handle_bind (ε := ε) S T (β := .snoc β (Answer a c k)) branches hb (.bv (ι := 0))).hasType.1
  have h' := Equiv.bindLetCase (pureEff := (⊥ : ε)) hv hl hr hc
  rw [underBinder_handle] at h'
  exact h.trans (h'.trans (.case (.refl hv)
    (handle_bind S T branches hb hl).symm (handle_bind S T branches hb hr).symm))


private theorem encode_at_typed {β : BoundCtx (Ty α) m} (hs : ∀ i, β.get i = .base (target i))
    (e : ε) (b : Body S T a c k grade ss) (hb : b.WellTyped S T e)
    (σ : Sequence.TreeSubst S ss target) (hσ : ∀ i, DeclaredPure (ε := ε) S (σ i)) :
    TE β ((b.encode S T).bsubst (fun i => treeNative S (σ i))) (Answer a c k) e := by
  let _ := endpoints S T
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  let src := BoundCtx.ofFin (fun i => Ty.base (ss i))
  have he := encode_typed S T (β := src) (fun i => congrFun (BoundCtx.get_ofFin _) i) e b hb
  apply he.bsubst_bot
  intro i
  rw [show src.get i = .base (ss i) from congrFun (BoundCtx.get_ofFin _) i]
  exact ⟨tree_type S T hs (σ i), (tree_pure S (σ i) (hσ i)).hasEffect⟩

private theorem handle_step {β : BoundCtx (Ty α) m} (hs : ∀ i, β.get i = .base (target i))
    (p : Controller S T a c k) (e : ε) (hp : ∀ j, Body.WellTyped S T e (p j))
    (b : Body S T a c k grade ss) (hb : b.WellTyped S T e)
    (σ : Sequence.TreeSubst S ss target) (hσ : ∀ i, DeclaredPure (ε := ε) S (σ i)) :
    EQ β (handle (fun j => (p j).encode S T) ((b.encode S T).bsubst (fun i => treeNative S (σ i))))
      (Scoped.Step.native (ε := ε) S T (@entryRank _ _ S a k ε _ _) (fun _ => p.loop S T)
        (b.toStep S T e hb σ hσ)) (.base c) := by
  let _ := endpoints S T
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  have hbr := fun j => (template_typed S T p e hp j).1
  induction b generalizing m with
  | done v =>
    simp only [Body.encode, Tm.bsubst, tree_bsubst, Body.toStep]
    exact handle_done S T _ hbr (tree_type S T hs _) (tree_pure S _ (Sequence.tree_pure_subst S v hb σ hσ))
  | again j hj v =>
    simp only [Body.encode, Tm.bsubst, tag_bsubst, tree_bsubst, Body.toStep]
    exact handle_again S T _ hbr (tag_type S T (tree_type S T hs _) j)
      (tag_pure (tree_pure S _ (Sequence.tree_pure_subst S v hb σ hσ)) j)
  | atom f args next ih =>
    simp only [Body.encode, Tm.bsubst, tuple_bsubst, tree_bsubst, Body.toStep, Scoped.Step.native]
    rw [lift_tree_bsubst (Ψ := Ψ) S σ (S.out f)]
    have hv := tuple_type S T (S.arity f) (S.arg f) _
      (fun i => tree_type S T hs ((args i).interpret S _ Tree.op σ))
    have ht := (encode_at_typed S T (slots_snoc hs (S.out f)) e next hb.2.2.2
      (Sequence.liftSubst S σ (S.out f)) (Body.liftSubst_pure S σ hσ _)).1
    exact (handle_let S T _ hbr (.op hv) ht).trans
      (.let₁ (.refl (.op hv)) (ih (slots_snoc hs _) hb.2.2.2 _ (Body.liftSubst_pure S σ hσ _)))
  | sum g args left right ihl ihr =>
    simp only [Body.encode, Tm.bsubst, tuple_bsubst, tree_bsubst, Body.toStep, Scoped.Step.native]
    conv in ((left.encode S T).bsubst _) => rw [lift_tree_bsubst (Ψ := Ψ) S σ (T.left g)]
    conv in ((right.encode S T).bsubst _) => rw [lift_tree_bsubst (Ψ := Ψ) S σ (T.right g)]
    have hv := tuple_type S T (T.arity g) (T.arg g) _
      (fun i => tree_type S T hs ((args i).interpret S _ Tree.op σ))
    have hl := (encode_at_typed S T (slots_snoc hs (T.left g)) e left hb.2.2.1
      (Sequence.liftSubst S σ (T.left g)) (Body.liftSubst_pure S σ hσ _)).1
    have hr := (encode_at_typed S T (slots_snoc hs (T.right g)) e right hb.2.2.2
      (Sequence.liftSubst S σ (T.right g)) (Body.liftSubst_pure S σ hσ _)).1
    have hop : HT β (.op (.inr g) _) (.coprod (.base (T.left g)) (.base (T.right g))) := .op hv
    exact (handle_case S T _ hbr hop hl hr).trans
      (.case (.refl hop)
        (ihl (slots_snoc hs _) hb.2.2.1 _ (Body.liftSubst_pure S σ hσ _))
        (ihr (slots_snoc hs _) hb.2.2.2 _ (Body.liftSubst_pure S σ hσ _)))

public theorem unfold {β : BoundCtx (Ty α) n} (hs : ∀ i, β.get i = .base (ss i))
    (p : Controller S T a c k) (e : ε) (hp : ∀ j, Body.WellTyped S T e (p j))
    (i : Entry S ε a k ss) :
    EQ β (p.loop S T i) (Scoped.Step.native (ε := ε) S T (@entryRank _ _ S a k ε _ _)
      (p.system S T e hp).endpoint ((p.system S T e hp).step ss i)) (.base c) := by
  let _ := endpoints S T
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  let branches := fun j => (p j).encode S T
  have hbr := fun j => (template_typed S T p e hp j).1
  have hv := tree_type S T hs i.payload
  have hpure := tree_pure (Ψ := Ψ) S i.payload i.pure
  have htag := tag_type S T hv i.pc
  have ht := (loopBody_typed S T (β := β) p e hp).1
  have hfix := Equiv.fixpoint (pureEff := (⊥ : ε)) htag ht
  have hrestart (m : Nat) : (p.loopBody S T m).underBinder = p.loopBody S T (m + 1) := by
    simp [Controller.loopBody, Tm.underBinder, rename_dispatch, Tm.rename]
  rw [hrestart, hrestart] at hfix
  have he := (handle_bind (ε := ε) S T branches hbr ht).hasType.1
  have hbeta := Equiv.letBeta (tag_pure hpure i.pc) htag he
  have hstart : (handle branches (p.loopBody S T n)).instantiate (tag i.pc (treeNative S i.payload)) =
      handle branches (dispatch k branches (tag i.pc (treeNative S i.payload))) := by
    simp [Controller.loopBody, branches, Tm.instantiate, handle_bsubst, dispatch_bsubst, Tm.bsubst]
  rw [hstart] at hbeta
  have hselect := dispatch_tag S T branches hbr hv hpure i.pc
  exact hfix.trans (hbeta.trans
    ((Equiv.case hselect (.refl .bv) (.refl (.iter .bv (dispatch_type S T branches hbr .bv)))).trans
      (handle_step S T hs p e hp (p i.pc) (hp i.pc) (fun _ => i.payload) (fun _ => i.pure))))

public theorem checked (p : Controller S T a c k) (e : ε) (he : IsIterative e)
    (hp : ∀ j, Body.WellTyped S T e (p j)) :
    Scoped.System.Checked S T (@entryRank _ _ S a k ε _ _) (p.system S T e hp) e := by
  let _ := endpoints S T
  let _ : HasEff (Φ ⊕ Ψ) ε := effects
  refine ⟨fun _ i => step_typed S T e (p i.pc) (hp i.pc) (fun _ => i.payload) (fun _ => i.pure), ?_, ?_⟩
  · intro Γ ss _ hs i
    have hty : ∀ j, Γ.toBoundCtx.get j = .base (ss j) := fun j =>
      (EffectCtx.get_toBoundCtx Γ j).trans (hs j)
    have hv := tree_type S T hty i.payload
    have hpure := tree_pure (Ψ := Ψ) S i.payload i.pure
    exact HasTypeEffect.iter he ⟨tag_type S T hv i.pc, (tag_pure hpure i.pc).hasEffect.mono bot_le⟩
      (loopBody_typed S T p e hp)
  · intro Γ ss _ hs i
    exact .equiv (unfold S T (fun j => (EffectCtx.get_toBoundCtx Γ j).trans (hs j)) p e hp i)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Compile.Proofs
