module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Thms

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation AbortEquiv)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape.Proofs

universe u v w r

variable {α : Type u}

public theorem exists_shape (V : α → Type v) {A : Ty α} (reply : Ty.denote V A) :
    ∃ (n : Nat) (ss : Fin n → α) (shape : ReplyShape ss A) (vars : (i : Fin n) → V (ss i)),
      shape.denote V vars = reply := by
  induction A with
  | base a => exact ⟨1, _, .atom a, fun _ => reply, rfl⟩
  | unit =>
    cases reply
    exact ⟨0, Fin.elim0, .unit, fun i => i.elim0, rfl⟩
  | empty => cases reply
  | coprod A B ihA ihB =>
    cases reply with
    | inl a =>
      obtain ⟨n, ss, s, vars, rfl⟩ := ihA a
      exact ⟨n, ss, .inl s, vars, rfl⟩
    | inr b =>
      obtain ⟨n, ss, s, vars, rfl⟩ := ihB b
      exact ⟨n, ss, .inr s, vars, rfl⟩
  | product A B ihA ihB =>
    obtain ⟨a, b⟩ := reply
    obtain ⟨n, ss, s, vs, rfl⟩ := ihA a
    obtain ⟨m, ts, t, ws, rfl⟩ := ihB b
    let slots : Fin (n + m) → α := Fin.addCases ss ts
    let vars : (i : Fin (n + m)) → V (slots i) :=
      Fin.addCases (motive := fun i => V (slots i))
        (fun i => cast (congrArg V (Fin.addCases_left (motive := fun _ => α)
          (left := ss) (right := ts) i).symm) (vs i))
        (fun i => cast (congrArg V (Fin.addCases_right (motive := fun _ => α)
          (left := ss) (right := ts) i).symm) (ws i))
    refine ⟨n + m, slots, .pair s t, vars, ?_⟩
    simp [ReplyShape.denote, vars]
    rfl

variable {n m : Nat} {ss : Fin n → α} {A : Ty α} (s : ReplyShape ss A) (place : Fin n → Fin m)

public theorem lowers {Φ : Type w} : (s.source (Φ := Φ) place).toLetIter m = some (s.native place) := by
  induction s with
  | atom _ => simp [ReplyShape.source, ReplyShape.native, Expr.toLetIter]
  | unit => rfl
  | pair _ _ ihL ihR => simp [ReplyShape.source, ReplyShape.native, Expr.toLetIter, ihL, ihR]
  | inl _ ih => simp [ReplyShape.source, ReplyShape.native, Expr.toLetIter, ih]
  | inr _ ih => simp [ReplyShape.source, ReplyShape.native, Expr.toLetIter, ih]

public theorem wf {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε] [Preorder ε] [OrderBot ε]
    {Γ : EffectCtx (Ty α) ε} (place : Fin n → Fin Γ.length)
    (hs : ∀ i, Γ.get (place i) = (.base (ss i), (⊥ : ε))) :
    Wf Γ (s.source place : Expr Φ) A (⊥ : ε) := by
  induction s with
  | atom a =>
    have h : (Γ.get (place 0)).2 ≤ (⊥ : ε) := by rw [hs 0]
    have hty : (Γ.get (place 0)).1 = .base a := congrArg Prod.fst (hs 0)
    simpa only [hty, ReplyShape.source] using (Wf.var (Φ := Φ) (place 0) h)
  | unit => exact .unit _ _
  | pair _ _ ihL ihR =>
    exact .pair (ihL _ (fun i => by simp only [hs, Fin.addCases_left]))
      (ihR _ (fun i => by simp only [hs, Fin.addCases_right]))
  | inl _ ih => exact .inl (ih place hs)
  | inr _ ih => exact .inr (ih place hs)

section Denotation

variable {Φ : Type w} [HasTy Φ (Ty α)] (V : α → Type v)
  {M : Type v → Type v} [Monad M] [LawfulMonad M] [Iterate M]
  (instr : InstructionModel (Ty.denote V) Φ M) {β : BoundCtx (Ty α) m}

omit [LawfulMonad M] in
private theorem denote_cast_bv (i : Fin m) {B : Ty α} (h : β.get i = B)
    (ρ : BoundEnv (Ty.denote V) β) :
    (cast (congrArg (Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β (.bv i)) h)
      (Derivation.bv (ι := i))).denote (Ty.denote V) instr (fun x => x.elim) ρ =
      pure (h ▸ ρ i) := by
  cases h
  rfl

public theorem denote_derivation (ht : ∀ i, β.get (place i) = .base (ss i))
    (ρ : BoundEnv (Ty.denote V) β) (vars : (i : Fin n) → V (ss i))
    (hρ : ∀ i, HEq (ρ (place i)) (vars i)) :
    (s.derivation (Φ := Φ) place ht).denote (Ty.denote V) instr (fun x => x.elim) ρ =
      pure (s.denote V vars) := by
  induction s with
  | atom _ =>
    rw [ReplyShape.derivation, denote_cast_bv V instr (place 0) (ht 0), ReplyShape.denote]
    congr 1
    exact eq_of_heq ((eqRec_heq (ht 0) (ρ (place 0))).trans (hρ 0))
  | unit => rfl
  | pair l r ihL ihR =>
    simp only [ReplyShape.derivation, Derivation.denote, ReplyShape.denote]
    rw [ihL, pure_bind, ihR, pure_bind]
    · rfl
    · intro i
      exact (hρ _).trans (cast_heq _ _).symm
    · intro i
      exact (hρ _).trans (cast_heq _ _).symm
  | inl _ ih =>
    simp only [ReplyShape.derivation, Derivation.denote, ReplyShape.denote, ih place ht vars hρ, pure_bind]
    rfl
  | inr _ ih =>
    simp only [ReplyShape.derivation, Derivation.denote, ReplyShape.denote, ih place ht vars hρ, pure_bind]
    rfl

end Denotation

omit place in
public theorem lift_denote (V : α → Type u) (vars : (i : Fin n) → V (ss i)) :
    (toSmall V A).symm (s.denote V vars) =
      s.denote (Lifted V) (fun i => ⟨vars i⟩) := by
  have liftCast {a b : α} (h : a = b) (x : V a) :
      cast (congrArg (Lifted V) h) (ULift.up x) = (ULift.up (cast (congrArg V h) x) : Lifted V b) := by
    cases h
    rfl
  induction s with
  | atom _ => rfl
  | unit => rfl
  | @pair _ _ _ _ A B l r ihL ihR =>
    change ((toSmall V A).symm (l.denote V _), (toSmall V B).symm (r.denote V _)) =
      (l.denote (Lifted V) _, r.denote (Lifted V) _)
    rw [ihL, ihR]
    simp [liftCast]
  | @inl _ _ A B shape ih =>
    change Sum.inl ((toSmall V A).symm (shape.denote V vars)) =
      (Sum.inl (shape.denote (Lifted V) (fun i => ⟨vars i⟩)) : Ty.denote (Lifted V) (.coprod A B))
    rw [ih]
  | @inr _ _ A B shape ih =>
    change Sum.inr ((toSmall V B).symm (shape.denote V vars)) =
      (Sum.inr (shape.denote (Lifted V) (fun i => ⟨vars i⟩)) : Ty.denote (Lifted V) (.coprod A B))
    rw [ih]

omit place s in
public theorem eval_bind_eq_iff_shapes {Φ : Type u} [HasTy Φ (Ty α)] (V : α → Type u)
    {ε : Type r} [HasEff Φ ε] [Bot ε] (P : PureMaps (Φ := Φ) (ε := ε) V)
    {B : Type (u + 1)} {f : Φ} (hf : ¬ IsPure (⊥ : ε) f)
    {x y : Ty.denote (Lifted V) (instrSrc f)}
    {k l : Ty.denote (Lifted V) (instrTrg f) → ITree.Tree (Event (Φ := Φ) V) B} :
    ((instructions V P).eval f x >>= k) = ((instructions V P).eval f y >>= l) ↔
      x = y ∧ ∀ {n : Nat} {ss : Fin n → α} (s : ReplyShape ss (instrTrg f)) (vars : (i : Fin n) → V (ss i)),
        k ((toSmall V (instrTrg f)).symm (s.denote V vars)) =
          l ((toSmall V (instrTrg f)).symm (s.denote V vars)) := by
  rw [eval_bind_eq_iff V P hf]
  refine ⟨fun ⟨h, hkl⟩ => ⟨h, fun s vars => hkl (s.denote V vars)⟩, ?_⟩
  rintro ⟨h, hkl⟩
  refine ⟨h, fun reply => ?_⟩
  obtain ⟨_, _, s, vars, rfl⟩ := exists_shape V reply
  exact hkl s vars

public theorem letOp_observations_of_abortEquiv {Φ : Type u} [HasTy Φ (Ty α)] [DecidableEq α] (V : α → Type u)
    {ε : Type r} [HasEff Φ ε] [Bot ε] (P : PureMaps (Φ := Φ) (ε := ε) V)
    {n : Nat} {β : BoundCtx (Ty α) n} {f : Φ} (hf : ¬ IsPure (⊥ : ε) f)
    {a b : Tm Empty Φ n} {k l : Tm Empty Φ (n + 1)} {B : Ty α}
    (da : Derivation Φ .nil β a (instrSrc f)) (db : Derivation Φ .nil β b (instrSrc f))
    (dk : Derivation Φ .nil (β.snoc (instrTrg f)) k B) (dl : Derivation Φ .nil (β.snoc (instrTrg f)) l B)
    (ρ : BoundEnv (Ty.denote (Lifted V)) β)
    {x y : Ty.denote (Lifted V) (instrSrc f)}
    (ha : da.denote (Ty.denote (Lifted V)) (instructions V P) (fun z => z.elim) ρ = pure x)
    (hb : db.denote (Ty.denote (Lifted V)) (instructions V P) (fun z => z.elim) ρ = pure y)
    (h : AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) β (.let₁ (.op f a) k) (.let₁ (.op f b) l) B) :
    x = y ∧ ∀ {m : Nat} {ss : Fin m → α} (shape : ReplyShape ss (instrTrg f)) (vars : (i : Fin m) → V (ss i)),
      let reply := (toSmall V (instrTrg f)).symm (shape.denote V vars)
      dk.denote (Ty.denote (Lifted V)) (instructions V P) (fun z => z.elim) (ρ.snoc reply) =
        dl.denote (Ty.denote (Lifted V)) (instructions V P) (fun z => z.elim) (ρ.snoc reply) := by
  apply (eval_bind_eq_iff_shapes V P hf (x := x) (y := y)
    (k := fun reply => dk.denote (Ty.denote (Lifted V)) (instructions V P) (fun z => z.elim) (ρ.snoc reply))
    (l := fun reply => dl.denote (Ty.denote (Lifted V)) (instructions V P) (fun z => z.elim) (ρ.snoc reply))).mp
  simpa only [Derivation.denote, ha, hb, pure_bind] using
    sound V P h (.let₁ (.op da) dk) (.let₁ (.op db) dl) ρ

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape.Proofs
