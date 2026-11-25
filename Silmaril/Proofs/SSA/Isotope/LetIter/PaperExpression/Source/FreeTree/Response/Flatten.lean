module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Bind.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.CallByValue.Thms

/-! # Source correctness and reflection for typed call-by-value flattening -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten.Proofs

universe u r

variable {α Φ : Type u} (S : Signature α Φ) {f : Φ}
  {n : Nat} {slots : Fin n → α} {c : α}

private theorem tuple_at_arity {m k : Nat} {as : Fin m → α} (h : m = k)
    (xs : (i : Fin k) → Tree S slots (as (i.cast h.symm))) :
    sourceTuple m (fun i => (argsAtArity S h xs i).source) =
      sourceTuple k (fun i => (xs i).source) := by
  cases h
  rfl

private theorem input_at_arity {m k : Nat} (as : Fin m → α) (h : m = k) :
    input m as = input k (fun i => as (i.cast h.symm)) := by
  cases h
  rfl

private theorem source_unary_args (h : S.arity f = 1) (p : Tree S slots (argSort S h 0)) :
    (Tree.op f (unaryArgs S h p)).source = .op f (.pair p.source .unit) := by
  simp only [Tree.source, unaryArgs, tuple_at_arity S]
  rfl

private theorem source_binary_args (h : S.arity f = 2)
    (p : Tree S slots (argSort S h 0)) (q : Tree S slots (argSort S h 1)) :
    (Tree.op f (binaryArgs S h p q)).source = .op f (.pair p.source (.pair q.source .unit)) := by
  simp only [Tree.source, binaryArgs, tuple_at_arity S]
  rfl

section Typed

variable {ε : Type r} [HasEff Φ ε] [Preorder ε] [Bot ε]

omit [Preorder ε] in
private theorem pure_at_arity {m k : Nat} {as : Fin m → α} (h : m = k)
    (xs : (i : Fin k) → Tree S slots (as (i.cast h.symm)))
    (hp : ∀ i, DeclaredPure (ε := ε) S (xs i)) :
    ∀ i, DeclaredPure (ε := ε) S (argsAtArity S h xs i) := by
  cases h
  exact hp

omit [Preorder ε] in
private theorem pure_unary_args (h : S.arity f = 1) (p : Tree S slots (argSort S h 0))
    (hp : DeclaredPure (ε := ε) S p) :
    ∀ i, DeclaredPure (ε := ε) S (unaryArgs S h p i) := by
  apply pure_at_arity S
  intro i
  refine Fin.cases ?_ (fun j => j.elim0) i
  exact hp

omit [Preorder ε] in
private theorem pure_binary_args (h : S.arity f = 2)
    (p : Tree S slots (argSort S h 0)) (q : Tree S slots (argSort S h 1))
    (hp : DeclaredPure (ε := ε) S p) (hq : DeclaredPure (ε := ε) S q) :
    ∀ i, DeclaredPure (ε := ε) S (binaryArgs S h p q i) := by
  apply pure_at_arity S
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hp
  · refine Fin.cases ?_ (fun k => k.elim0) j
    exact hq

private theorem emit_typed {e : ε} (args : Args S slots f)
    (hf : instrEff f ≤ e) (hargs : ∀ i, DeclaredPure (ε := ε) S (args i)) :
    Sequence.WellTyped S e (emit (ε := ε) S f args) := by
  classical
  by_cases h : IsPure (⊥ : ε) f
  · simp only [emit, ite_eq_left h, Sequence.WellTyped, DeclaredPure]
    exact ⟨h, hargs⟩
  · simp only [emit, ite_eq_right h, Sequence.WellTyped, DeclaredPure]
    exact ⟨hargs, h, hf, trivial⟩

private theorem unary_tail_typed {e : ε} (h : S.arity f = 1) (hf : instrEff f ≤ e) :
    Sequence.WellTyped S e (unaryTail (ε := ε) S (slots := slots) f h) :=
  emit_typed S _ hf (pure_unary_args S (slots := extendSorts (argSort S h 0) slots) h (.var 0) trivial)

private theorem binary_tail_typed {e : ε} (h : S.arity f = 2) (hf : instrEff f ≤ e) :
    Sequence.WellTyped S e (binaryTail (ε := ε) S (slots := slots) f h) :=
  emit_typed S _ hf (pure_binary_args S
    (slots := extendSorts (argSort S h 1) (extendSorts (argSort S h 0) slots))
      h (.var (0 : Fin (n + 1)).succ) (.var 0) trivial trivial)

public theorem compile_typed (e : ε) (p : Program S slots c) (hp : Program.WellTyped S e p) :
    Sequence.WellTyped S e (compile (ε := ε) S p) := by
  induction p with
  | tree t => exact hp
  | let1 p q ihp ihq => exact Sequence.bind_typed S e _ _ (ihp hp.1) (ihq hp.2)
  | request f args => exact emit_typed S args hp.1 hp.2
  | unary f h p ih =>
    exact Sequence.bind_typed S e _ _ (ih hp.2) (unary_tail_typed S h hp.1)
  | binary f h p q ihp ihq =>
    exact Sequence.bind_typed S e _ _ (ihp hp.2.1)
      (Sequence.bind_typed S e _ _ (Sequence.weaken_typed S _ e _ (ihq hp.2.2))
        (binary_tail_typed S h hp.1))

end Typed

section Soundness

variable {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε]

private theorem extended_pure {Γ : EffectCtx (Ty α) ε} (hΓ : Γ.Pure) (x : α) :
    EffectCtx.Pure ((Ty.base x, (⊥ : ε)) :: Γ) :=
  fun i => Fin.cases (motive := fun j => (((Ty.base x, (⊥ : ε)) :: Γ).get j).2 = ⊥)
    rfl hΓ i

private theorem extended_slots {Γ : EffectCtx (Ty α) ε} {ts : Fin Γ.length → α}
    (hslots : ∀ i, (Γ.get i).1 = .base (ts i)) (x : α) :
    ∀ i : Fin (Γ.length + 1),
      (((Ty.base x, (⊥ : ε)) :: Γ).get i).1 = .base (extendSorts x ts i) :=
  fun i => Fin.cases (motive := fun j =>
    (((Ty.base x, (⊥ : ε)) :: Γ).get j).1 = .base (extendSorts x ts j)) rfl hslots i

variable {Γ : EffectCtx (Ty α) ε} {ts : Fin Γ.length → α} {e : ε}

private theorem emit_eqv
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (ts i))
    (args : Args S ts f) (hf : instrEff f ≤ e)
    (hargs : ∀ i, DeclaredPure (ε := ε) S (args i)) :
    letI := S.endpoints
    Eqv Γ (.base (S.out f)) e (Tree.op f args).source ((emit (ε := ε) S f args).source) := by
  classical
  let instr := S.endpoints
  have ht := SingleCall.request_wf S args hargs hΓ hs hf
  by_cases h : IsPure (⊥ : ε) f
  · simp only [emit, ite_eq_left h, Sequence.source]
    exact .refl ht
  · simp only [emit, ite_eq_right h, Sequence.source]
    exact (Eqv.step (.rewrite (.let₁ ht (.var 0 bot_le)) ht (.let1_eta _))).symm

private theorem unary_input (h : S.arity f = 1) :
    letI := S.endpoints
    instrSrc f = product (Ty.base (argSort S h 0)) (unit : Ty α) :=
  input_at_arity (S.arg f) h

private theorem binary_input (h : S.arity f = 2) :
    letI := S.endpoints
    instrSrc f = product (Ty.base (argSort S h 0)) (product (Ty.base (argSort S h 1)) (unit : Ty α)) :=
  input_at_arity (S.arg f) h

private theorem unary_eqv (h : S.arity f = 1) (hf : instrEff f ≤ e)
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (ts i))
    (p : Sequence S (argSort S h 0) ts) (hp : Sequence.WellTyped S e p) :
    letI := S.endpoints
    Eqv Γ (.base (S.out f)) e (.op f (.pair p.source .unit))
      ((Sequence.bind S p (unaryTail (ε := ε) S f h)).source) := by
  let instr := S.endpoints
  let x := argSort S h 0
  let Δ : EffectCtx (Ty α) ε := (Ty.base x, (⊥ : ε)) :: Γ
  have hw := Sequence.wf S hΓ hs e p hp
  have hin := unary_input S h
  have hpair := CallByValue.pair_unit_bind hw
  have hv : Wf Δ (.pair (.var 0) .unit : Expr Φ) (product (Ty.base x) (unit : Ty α)) e :=
    .pair (.var 0 bot_le) (.unit _ _)
  have h1 := Eqv.op (f := f) hf (hin.symm ▸ hpair)
  have h2 := CallByValue.op_let hf hw (hin.symm ▸ hv)
  let v : Tree S (extendSorts x ts) x := .var 0
  have he := emit_eqv S (Γ := Δ) (ts := extendSorts x ts) (extended_pure hΓ x)
    (extended_slots hs x) (unaryArgs S h v) hf (pure_unary_args S h v trivial)
  have h3 := (source_unary_args S h v) ▸ he
  exact h1.trans (h2.trans ((Eqv.let1 (.refl hw) h3).trans
    (Sequence.bind_eqv S hΓ hs e p _ hp (unary_tail_typed S h hf))))

private theorem binary_eqv (h : S.arity f = 2) (hf : instrEff f ≤ e)
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (ts i))
    (p : Sequence S (argSort S h 0) ts) (q : Sequence S (argSort S h 1) ts)
    (hp : Sequence.WellTyped S e p) (hq : Sequence.WellTyped S e q) :
    letI := S.endpoints
    Eqv Γ (.base (S.out f)) e (.op f (.pair p.source (.pair q.source .unit)))
      ((Sequence.bind S p (Sequence.bind S (Sequence.weaken S (argSort S h 0) q)
        (binaryTail (ε := ε) S f h))).source) := by
  let instr := S.endpoints
  let x := argSort S h 0
  let y := argSort S h 1
  let Δ : EffectCtx (Ty α) ε := (Ty.base x, (⊥ : ε)) :: Γ
  let Θ : EffectCtx (Ty α) ε := (Ty.base y, (⊥ : ε)) :: Δ
  let tsΔ := extendSorts x ts
  let tsΘ := extendSorts y tsΔ
  let q' := Sequence.weaken S x q
  let tail := binaryTail (ε := ε) S (slots := ts) f h
  have hΔ := extended_pure hΓ x
  have hΘ : Θ.Pure := extended_pure hΔ y
  have hsΔ : ∀ i : Fin Δ.length, (Δ.get i).1 = .base (tsΔ i) := extended_slots hs x
  have hsΘ : ∀ i : Fin Θ.length, (Θ.get i).1 = .base (tsΘ i) :=
    extended_slots (Γ := Δ) (ts := tsΔ) hsΔ y
  have hwp := Sequence.wf S hΓ hs e p hp
  have hwq := Sequence.wf S hΓ hs e q hq
  have hq' := Sequence.weaken_typed S x e q hq
  have hwq' := Sequence.wf S hΔ hsΔ e q' hq'
  have htail := binary_tail_typed S (slots := ts) h hf
  have hin := binary_input S h
  have hv : Wf Θ (.pair (.var 1) (.pair (.var 0) .unit) : Expr Φ)
      (product (Ty.base x) (product (Ty.base y) (unit : Ty α))) e :=
    .pair (.var 1 bot_le) (.pair (.var 0 bot_le) (.unit _ _))
  have hv' : Wf Θ (.pair (.var 1) (.pair (.var 0) .unit) : Expr Φ) (instrSrc f) e :=
    hin.symm ▸ hv
  have hwk := CallByValue.wf_wk0 hwq (Ty.base x, (⊥ : ε))
  have h1 := Eqv.op (f := f) hf (hin.symm ▸ CallByValue.pair_two_bind hwp hwq)
  have h2 := CallByValue.op_let hf hwp (.let₁ hwk hv')
  have h3 := Eqv.let1 (.refl hwp) (CallByValue.op_let hf hwk hv')
  let v : Tree S tsΘ x := .var (0 : Fin (Γ.length + 1)).succ
  let w : Tree S tsΘ y := .var 0
  have he := emit_eqv S (Γ := Θ) (ts := tsΘ) hΘ hsΘ (binaryArgs S h v w) hf
    (pure_binary_args S h v w trivial trivial)
  have h4 := (source_binary_args S h v w) ▸ he
  have hinner : Eqv Δ (.base (S.out f)) e
      (.let₁ q'.source (.op f (.pair (.var 1) (.pair (.var 0) .unit))))
      ((Sequence.bind S q' tail).source) :=
    (Eqv.let1 (.refl hwq') h4).trans (Sequence.bind_eqv S hΔ hsΔ e q' tail hq' htail)
  have hinner' := (Sequence.weaken_source S q x) ▸ hinner
  have houter := Sequence.bind_eqv S hΓ hs e p (Sequence.bind S q' tail) hp
    (Sequence.bind_typed S e q' tail hq' htail)
  exact h1.trans (h2.trans (h3.trans ((Eqv.let1 (.refl hwp) hinner').trans houter)))

private theorem compile_eqv_aux (e : ε) (p : Program S slots c) (hp : Program.WellTyped S e p) :
    letI := S.endpoints
    ∀ {Γ : EffectCtx (Ty α) ε} (hlen : Γ.length = n), Γ.Pure →
      (∀ i : Fin Γ.length, (Γ.get i).1 = .base (slots (i.cast hlen))) →
      Eqv Γ (.base c) e p.source (compile (ε := ε) S p).source := by
  let instr := S.endpoints
  induction p with
  | @tree size ambient c p =>
    intro Γ hlen hΓ hs
    subst size
    exact .refl (tree_wf S p hp hΓ hs e)
  | @let1 size ambient a c p q ihp ihq =>
    intro Γ hlen hΓ hs
    subst size
    have hs' := extended_slots (ts := ambient) hs a
    exact (Eqv.let1 (ihp hp.1 rfl hΓ hs) (ihq hp.2 rfl (extended_pure hΓ a) hs')).trans
      (Sequence.bind_eqv S hΓ hs e _ _ (compile_typed S e p hp.1) (compile_typed S e q hp.2))
  | @request size ambient f args =>
    intro Γ hlen hΓ hs
    subst size
    exact emit_eqv S hΓ hs args hp.1 hp.2
  | @unary size ambient f h p ih =>
    intro Γ hlen hΓ hs
    subst size
    have he := Eqv.pair (ih hp.2 rfl hΓ hs) (.refl (Wf.unit Γ e))
    have hsrc := Eqv.op (f := f) hp.1 ((unary_input S h).symm ▸ he)
    exact hsrc.trans (unary_eqv S h hp.1 hΓ hs _ (compile_typed S e p hp.2))
  | @binary size ambient f h p q ihp ihq =>
    intro Γ hlen hΓ hs
    subst size
    have he := Eqv.pair (ihp hp.2.1 rfl hΓ hs)
      (.pair (ihq hp.2.2 rfl hΓ hs) (.refl (Wf.unit Γ e)))
    have hsrc := Eqv.op (f := f) hp.1 ((binary_input S h).symm ▸ he)
    exact hsrc.trans (binary_eqv S h hp.1 hΓ hs _ _
      (compile_typed S e p hp.2.1) (compile_typed S e q hp.2.2))

public theorem compile_eqv (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (ts i))
    (e : ε) (p : Program S ts c) (hp : Program.WellTyped S e p) :
    letI := S.endpoints
    Eqv Γ (.base c) e p.source (compile (ε := ε) S p).source :=
  compile_eqv_aux S e p hp rfl hΓ hs

end Soundness

section Reflection

variable {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] [DecidableEq α]
  {Γ : EffectCtx (Ty α) ε} {ts : Fin Γ.length → α}

public theorem endpoint_reflection (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (ts i))
    (e : ε) (p q : Program S ts c) (hp : Program.WellTyped S e p) (hq : Program.WellTyped S e q)
    {t s : Tm Empty Φ Γ.length}
    (ht : p.source.toLetIter Γ.length = some t) (ht' : q.source.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base c) ↔
      Eqv Γ (.base c) e p.source q.source := by
  let instr := S.endpoints
  refine ⟨fun hn => ?_, fun he => he.toLetIter ht ht'⟩
  let p' := compile (ε := ε) S p
  let q' := compile (ε := ε) S q
  have el := compile_eqv S hΓ hs e p hp
  have er := compile_eqv S hΓ hs e q hq
  have hl := el.toLetIter ht (Sequence.lowers S p')
  have hr := er.toLetIter ht' (Sequence.lowers S q')
  have hflat := (Sequence.endpoint_reflection S hΓ hs e p' q'
    (compile_typed S e p hp) (compile_typed S e q hq)).mp (hl.symm.trans (hn.trans hr))
  exact el.trans (hflat.trans er.symm)

end Reflection

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten.Proofs
