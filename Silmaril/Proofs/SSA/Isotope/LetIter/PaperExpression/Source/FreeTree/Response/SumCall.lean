module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Thms

/-! # Observe one sum request and reflect its two straight-line continuations -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.Semantics Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall.Proofs

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α} {c : α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "β" => Γ.toBoundCtx
local notation "D[" ss "]" => Ty.denote (Atom S ss)
local notation "M[" ss "]" => instructions (ε := ε) S T ss

omit [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] in
private theorem tuple_lowers {k n : Nat} (a : Fin k → Expr (Φ ⊕ Ψ)) (t : Fin k → Tm Empty (Φ ⊕ Ψ) n)
    (h : ∀ i, (a i).toLetIter n = some (t i)) :
    (sourceTuple k a).toLetIter n = some (nativeTuple k t) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [sourceTuple, nativeTuple, Expr.toLetIter, h 0, Option.bind_some,
      ih (fun i => a i.succ) (fun i => t i.succ) (fun i => h i.succ), Option.map_some]

omit [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] in
private theorem tree_lowers {n : Nat} {ss : Fin n → α} {a : α} (p : Tree S ss a) :
    (treeSource (Ψ := Ψ) S p).toLetIter n = some (treeNative (Ψ := Ψ) S p) := by
  induction p with
  | var i => simp [treeSource, treeNative, Expr.toLetIter, i.isLt]
  | op f args ih =>
    simp only [treeSource, treeNative, Expr.toLetIter, tuple_lowers _ _ ih, Option.map_some]

omit [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] in
private theorem arm_lowers {n : Nat} {ss : Fin n → α} (p : Sequence S c ss) :
    (armSource (Ψ := Ψ) S p).toLetIter n = some (armNative (Ψ := Ψ) S p) := by
  induction p with
  | ret p => exact tree_lowers S p
  | call f args next ih =>
    simp only [armSource, armNative, Expr.toLetIter, tuple_lowers _ _ (fun i => tree_lowers S (args i)),
      ih, Option.map_some, Option.bind_some]

omit [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] in
public theorem lowers {n : Nat} {ss : Fin n → α} (p : Program S T ss c) :
    p.source.toLetIter n = some p.native := by
  simp only [Program.source, Program.native, Expr.toLetIter,
    tuple_lowers _ _ (fun i => tree_lowers S (p.args i)), arm_lowers S p.left, arm_lowers S p.right,
    Option.map_some, Option.bind_some]

omit [HasEff Φ ε] [HasEff Ψ ε] in
private theorem slots_extended {a : α} (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) :
    ∀ i : Fin (Γ.length + 1),
      (((Ty.base a, (⊥ : ε)) :: Γ).get i).1 = .base (extendSorts a slots i) :=
  fun i => Fin.cases (motive := fun j =>
    (((Ty.base a, (⊥ : ε)) :: Γ).get j).1 = .base (extendSorts a slots j)) rfl hslots i

omit [HasEff Φ ε] [HasEff Ψ ε] in
private theorem pure_extended (hΓ : Γ.Pure) (a : α) :
    EffectCtx.Pure ((Ty.base a, (⊥ : ε)) :: Γ) :=
  fun i => Fin.cases (motive := fun j => (((Ty.base a, (⊥ : ε)) :: Γ).get j).2 = ⊥) rfl hΓ i

private theorem tuple_wf {k : Nat} {as : Fin k → α} {xs : Fin k → Expr (Φ ⊕ Ψ)} {e : ε}
    (hs : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; ∀ i, Wf Γ (xs i) (.base (as i)) e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf Γ (sourceTuple k xs) (input k as) e := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  induction k with
  | zero => exact .unit _ _
  | succ k ih => exact .pair (hs 0) (ih (fun i => hs i.succ))

private theorem tree_wf (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    {a : α} (p : Tree S slots a) (hp : DeclaredPure (ε := ε) S p) (e : ε) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf Γ (treeSource (Ψ := Ψ) S p) (.base a) e := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  induction p with
  | var i => exact hslots i ▸ Wf.var i ((hΓ i).trans_le bot_le)
  | op f args ih =>
    exact .op (f := (Sum.inl f : Φ ⊕ Ψ)) (hp.1.trans_le bot_le) (tuple_wf S T (fun i => ih i (hp.2 i)))

private theorem arm_wf_aux {n : Nat} {ss : Fin n → α} (e : ε)
    (p : Sequence S c ss) (hp : Sequence.WellTyped S e p) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ∀ {Γ : EffectCtx (Ty α) ε} (hlen : Γ.length = n), Γ.Pure →
      (∀ i : Fin Γ.length, (Γ.get i).1 = .base (ss (i.cast hlen))) →
      Wf Γ (armSource (Ψ := Ψ) S p) (.base c) e := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  induction p with
  | @ret size ambient p =>
    intro Γ hlen hΓ hslots
    subst size
    exact tree_wf S T hΓ hslots p hp e
  | @call size ambient f args next ih =>
    intro Γ hlen hΓ hslots
    subst size
    refine .let₁ (.op (f := (Sum.inl f : Φ ⊕ Ψ)) hp.2.2.1 (tuple_wf S T (fun i =>
      tree_wf S T hΓ hslots (args i) (hp.1 i) e))) ?_
    exact ih hp.2.2.2 rfl (pure_extended hΓ _) (slots_extended hslots)

public theorem source_wf (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (e : ε) (p : Program S T slots c) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf Γ p.source (.base c) e := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  exact .case (.op (f := (Sum.inr p.op : Φ ⊕ Ψ)) hp.2.1 (tuple_wf S T (fun i =>
    tree_wf S T hΓ hslots (p.args i) (hp.1 i) e)))
    (arm_wf_aux S T e p.left hp.2.2.1 rfl (pure_extended hΓ _) (slots_extended hslots))
    (arm_wf_aux S T e p.right hp.2.2.2 rfl (pure_extended hΓ _) (slots_extended hslots))

section Evaluation

variable {m : Nat} (modelSlots : Fin m → α)

local notation "D" => D[modelSlots]
local notation "M" => M[modelSlots]
local notation "free" => (fun x : Empty => x.elim)

omit [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] in
private def tupleDerivation {k : Nat} {as : Fin k → α} {ts : Fin k → Tm Empty (Φ ⊕ Ψ) Γ.length}
    (ds : letI := endpoints S T; ∀ i, Derivation (Φ ⊕ Ψ) Γ₀ β (ts i) (.base (as i))) :
    letI := endpoints S T
    Derivation (Φ ⊕ Ψ) Γ₀ β (nativeTuple k ts) (input k as) := by
  let instr := endpoints S T
  induction k with
  | zero => exact .unit
  | succ k ih => exact .pair (ds 0) (ih fun i => ds i.succ)

omit [HasEff Ψ ε] in
private theorem eval_tuple (ρ : BoundEnv D β) {k : Nat} {as : Fin k → α}
    {ts : Fin k → Tm Empty (Φ ⊕ Ψ) Γ.length}
    (ds : letI := endpoints S T; ∀ i, Derivation (Φ ⊕ Ψ) Γ₀ β (ts i) (.base (as i)))
    (xs : (i : Fin k) → Tree S modelSlots (as i))
    (he : letI := endpoints S T; ∀ i, (ds i).denote D M free ρ = ITree.ret ⟨xs i⟩) :
    letI := endpoints S T
    (tupleDerivation S T ds).denote D M free ρ = ITree.ret (packArgs S modelSlots k as xs) := by
  let instr := endpoints S T
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((ds 0).denote D M free ρ >>= fun x =>
      (tupleDerivation S T (fun i => ds i.succ)).denote D M free ρ >>= fun y =>
        ITree.ret (x, y)) = _
    rw [he 0, ih (fun i => ds i.succ) (fun i => xs i.succ) (fun i => he i.succ)]
    erw [pure_bind]
    erw [pure_bind]
    rfl

omit [HasEff Ψ ε] in
private theorem eval_cast_bv {i : Fin Γ.length} {A : Ty α}
    (h : (β).get i = A) (ρ : BoundEnv D β) (x : D A) (hx : ρ i = h.symm ▸ x) :
    letI := endpoints S T
    Derivation.denote D M (h ▸ Derivation.bv (Γ := Γ₀) (ι := i)) free ρ = ITree.ret x := by
  let instr := endpoints S T
  cases h
  exact congrArg ITree.ret hx

omit [HasEff Ψ ε] in
private theorem eval_tree_exists (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    {a : α} (p : Tree S slots a) (hp : DeclaredPure (ε := ε) S p) :
    letI := endpoints S T
    ∃ d : Derivation (Φ ⊕ Ψ) Γ₀ β (treeNative S p) (.base a),
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (slots i),
        d.denote D M free (variableEnv S modelSlots hslots vars) =
          ITree.ret ⟨p.interpret S (Tree S modelSlots) Tree.op vars⟩ := by
  let instr := endpoints S T
  classical
  induction p with
  | var i =>
    have hi := (EffectCtx.get_toBoundCtx Γ i).trans (hslots i)
    refine ⟨hi ▸ Derivation.bv, fun vars => ?_⟩
    exact eval_cast_bv S T modelSlots (A := .base (slots i)) hi (variableEnv S modelSlots hslots vars) ⟨vars i⟩ rfl
  | op f args ih =>
    choose ds hds using fun i => ih i (hp.2 i)
    refine ⟨.op (f := (Sum.inl f : Φ ⊕ Ψ)) (tupleDerivation S T ds), fun vars => ?_⟩
    change ((tupleDerivation S T ds).denote D M free _ >>= (M).eval (.inl f)) = _
    rw [eval_tuple S T modelSlots _ ds _ (fun i => hds i vars)]
    erw [pure_bind]
    simp only [instructions, ite_eq_left hp.1, readArgs, unpackArgs_packArgs]
    rfl

omit [HasEff Ψ ε] in
private theorem eval_args_exists (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    {k : Nat} {as : Fin k → α} (args : (i : Fin k) → Tree S slots (as i))
    (hp : ∀ i, DeclaredPure (ε := ε) S (args i)) :
    letI := endpoints S T
    ∃ d : Derivation (Φ ⊕ Ψ) Γ₀ β (nativeTuple k (fun i => treeNative S (args i))) (input k as),
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (slots i),
        d.denote D M free (variableEnv S modelSlots hslots vars) =
          ITree.ret (packArgs S modelSlots k as (fun i => (args i).interpret S _ Tree.op vars)) := by
  let instr := endpoints S T
  choose ds hds using fun i => eval_tree_exists S T modelSlots hslots (args i) (hp i)
  exact ⟨tupleDerivation S T ds, fun vars => eval_tuple S T modelSlots _ ds _ (fun i => hds i vars)⟩

omit [HasEff Ψ ε] in
private theorem eval_atom_visible (f : Φ) (args : Args S modelSlots f)
    (hf : ¬ IsPure (⊥ : ε) f) :
    letI := endpoints S T
    (M).eval (.inl f) (packArgs S modelSlots (S.arity f) (S.arg f) args) =
      ITree.vis (.atom f args) (fun r => ITree.ret ⟨r⟩) := by
  let instr := endpoints S T
  simp only [instructions, ite_eq_right hf, readArgs, unpackArgs_packArgs]

omit [HasEff Ψ ε] in
private theorem eval_sum_request (g : Ψ) (args : SumArgs S T modelSlots g) :
    letI := endpoints S T
    (M).eval (.inr g) (packArgs S modelSlots (T.arity g) (T.arg g) args) =
      ITree.vis (.sum g args) (fun r => ITree.ret (responseValue S T modelSlots r)) := by
  let instr := endpoints S T
  simp only [instructions, unpackArgs_packArgs]
  rfl

omit [HasEff Ψ ε] in
private theorem eval_arm_aux {n : Nat} {ss : Fin n → α} (e : ε)
    (p : Sequence S c ss) (hp : Sequence.WellTyped S e p) :
    letI := endpoints S T
    ∀ {Γ : EffectCtx (Ty α) ε} (hlen : Γ.length = n)
      (hslots : ∀ i : Fin Γ.length, (Γ.get i).1 = .base (ss (i.cast hlen))),
      ∃ d : Derivation (Φ ⊕ Ψ) Γ₀ Γ.toBoundCtx (hlen.symm ▸ armNative S p) (.base c),
        ∀ vars : (i : Fin n) → Tree S modelSlots (ss i),
          d.denote D M free (variableEnv S modelSlots hslots (fun i => vars (i.cast hlen))) =
            Sequence.denoteWith S modelSlots Event.atom p vars := by
  let instr := endpoints S T
  classical
  induction p with
  | @ret size ambient p =>
    intro Γ hlen hslots
    subst size
    exact eval_tree_exists S T modelSlots hslots p hp
  | @call size ambient f args next ih =>
    intro Γ hlen hslots
    subst size
    have ht := slots_extended (a := S.out f) hslots
    obtain ⟨d, hd⟩ := eval_args_exists S T modelSlots hslots args hp.1
    obtain ⟨d', hd'⟩ := ih hp.2.2.2 (Γ := (Ty.base (S.out f), (⊥ : ε)) :: Γ) rfl ht
    refine ⟨.let₁ (.op (f := (Sum.inl f : Φ ⊕ Ψ)) d) d', fun vars => ?_⟩
    let ρ := variableEnv S modelSlots hslots vars
    change ((d.denote D M free ρ >>= (M).eval (.inl f)) >>= fun r =>
      d'.denote D M free (ρ.snoc r)) = _
    rw [hd vars]
    erw [pure_bind]
    rw [eval_atom_visible S T modelSlots f _ hp.2.1, ITree.vis_bind]
    simp only [Sequence.denoteWith]
    congr 1
    funext r
    erw [pure_bind]
    let vals := extendValues S modelSlots r vars
    have hs := variableEnv_snoc S modelSlots hslots ht vals
    exact (congrArg (d'.denote D M free) hs).trans (hd' vals)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
public theorem eval_exists (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p : Program S T slots c) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    ∃ d : Derivation (Φ ⊕ Ψ) Γ₀ β p.native (.base c),
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (slots i),
        d.denote D M free (variableEnv S modelSlots hslots vars) = Program.denote S T modelSlots p vars := by
  let instr := endpoints S T
  obtain ⟨d, hd⟩ := eval_args_exists S T modelSlots hslots p.args hp.1
  have hL := slots_extended (a := T.left p.op) hslots
  have hR := slots_extended (a := T.right p.op) hslots
  obtain ⟨dl, hl⟩ := eval_arm_aux S T modelSlots e p.left hp.2.2.1 (Γ := (Ty.base (T.left p.op), (⊥ : ε)) :: Γ) rfl hL
  obtain ⟨dr, hr⟩ := eval_arm_aux S T modelSlots e p.right hp.2.2.2 (Γ := (Ty.base (T.right p.op), (⊥ : ε)) :: Γ) rfl hR
  refine ⟨.case (.op (f := (Sum.inr p.op : Φ ⊕ Ψ)) d) dl dr, fun vars => ?_⟩
  let ρ := variableEnv S modelSlots hslots vars
  erw [Derivation.denote, Derivation.denote]
  rw [hd vars]
  erw [pure_bind]
  rw [eval_sum_request S T modelSlots p.op, ITree.vis_bind]
  simp only [Program.denote]
  congr 1
  funext r
  erw [pure_bind]
  cases r with
  | inl a =>
    change dl.denote D M free (ρ.snoc ⟨a⟩) = _
    let vals := extendValues S modelSlots a vars
    have hs := variableEnv_snoc S modelSlots hslots hL vals
    exact (congrArg (dl.denote D M free) hs).trans (hl vals)
  | inr b =>
    change dr.denote D M free (ρ.snoc ⟨b⟩) = _
    let vals := extendValues S modelSlots b vars
    have hs := variableEnv_snoc S modelSlots hslots hR vals
    exact (congrArg (dr.denote D M free) hs).trans (hr vals)

end Evaluation

section Reflection

omit [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] in
public theorem eq_of_denote_eq {n : Nat} {ss : Fin n → α} {p q : Program S T ss c}
    (h : ∀ {m : Nat} (modelSlots : Fin m → α)
      (vars : (i : Fin n) → Tree S modelSlots (ss i)),
      Program.denote S T modelSlots p vars = Program.denote S T modelSlots q vars) :
    p = q := by
  cases p with
  | mk f args pl pr =>
    cases q with
    | mk g other ql qr =>
      have hreq := congrArg (fun t => (ITree.out t).map (fun
        | .ret _ => none
        | .vis e _ => sumLabel S T ss e)) (h ss Tree.var)
      simp only [Program.denote, ITree.out_vis, Part.map_some, Part.some_inj, sumLabel,
        Option.some.injEq, SingleCall.interpret_vars] at hreq
      have ho : f = g := congrArg Sigma.fst hreq
      subst g
      have ha : args = other := eq_of_heq (Sigma.mk.inj hreq).2
      subst other
      congr 1
      · apply Sequence.eq_of_denoteWith_eq S (E := fun ms => Event S T ms) (fun _ => Event.atom)
          (atomLabel S T) (fun _ _ _ => rfl)
        intro m modelSlots vars
        let rest := fun i : Fin n => vars i.succ
        have he := congrFun ((ITree.vis_inj
          (Event.sum f (fun i => (args i).interpret S (Tree S modelSlots) Tree.op rest)) _ _).mp
          (h modelSlots rest)) (Sum.inl (vars 0))
        have hv : extendValues S modelSlots (vars 0) rest = vars := by
          funext i
          exact Fin.cases rfl (fun _ => rfl) i
        exact (congrArg (fun vals => Sequence.denoteWith S modelSlots Event.atom pl vals =
          Sequence.denoteWith S modelSlots Event.atom ql vals) hv).mp he
      · apply Sequence.eq_of_denoteWith_eq S (E := fun ms => Event S T ms) (fun _ => Event.atom)
          (atomLabel S T) (fun _ _ _ => rfl)
        intro m modelSlots vars
        let rest := fun i : Fin n => vars i.succ
        have he := congrFun ((ITree.vis_inj
          (Event.sum f (fun i => (args i).interpret S (Tree S modelSlots) Tree.op rest)) _ _).mp
          (h modelSlots rest)) (Sum.inr (vars 0))
        have hv : extendValues S modelSlots (vars 0) rest = vars := by
          funext i
          exact Fin.cases rfl (fun _ => rfl) i
        exact (congrArg (fun vals => Sequence.denoteWith S modelSlots Event.atom pr vals =
          Sequence.denoteWith S modelSlots Event.atom qr vals) hv).mp he

variable [DecidableEq α]

omit [DecidableEq α] in
private theorem instructions_pure {m : Nat} (modelSlots : Fin m → α)
    (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    InstructionModel.RespectsPure (ε := ε) M[modelSlots] := by
  classical
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  intro f hf
  cases f with
  | inl f =>
    change IsPure (⊥ : ε) f at hf
    exact ⟨fun x => ⟨Tree.op f (readArgs S modelSlots f x)⟩, fun x => by
      simp only [instructions, ite_eq_left hf]; rfl⟩
  | inr g => exact (visible g hf).elim

public theorem native_eq_implies_eq (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Program S T slots c) (hp : Program.WellTyped S T e p) (hq : Program.WellTyped S T e q)
    (hn : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects
      AbortEquiv (⊥ : ε) Γ₀ β p.native q.native (.base c)) : p = q := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  apply eq_of_denote_eq S T
  intro m modelSlots vars
  obtain ⟨dp, hdp⟩ := eval_exists S T modelSlots hslots e p hp
  obtain ⟨dq, hdq⟩ := eval_exists S T modelSlots hslots e q hq
  have he := LetIter.Semantics.Categorical.denote_eq_of_abortEquiv_nil.{u, u + 2, u, r}
    (Atom S modelSlots) M[modelSlots] (instructions_pure S T modelSlots visible) hn dp dq
    (variableEnv S modelSlots hslots vars)
  exact (hdp vars).symm.trans (he.trans (hdq vars))

variable [EffectIteration ε]

public theorem endpoint_reflection (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Program S T slots c) (hp : Program.WellTyped S T e p) (hq : Program.WellTyped S T e q) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) Γ₀ β p.native q.native (.base c) ↔ Eqv Γ (.base c) e p.source q.source := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  refine ⟨fun hn => ?_, fun he => he.toLetIter (lowers S T p) (lowers S T q)⟩
  have he := native_eq_implies_eq S T visible hslots e p q hp hq hn
  subst q
  exact .refl (source_wf S T hΓ hslots e p hp)

end Reflection

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall.Proofs
