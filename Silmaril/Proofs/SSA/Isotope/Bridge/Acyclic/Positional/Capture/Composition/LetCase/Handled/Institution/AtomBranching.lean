module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Defs
import Silmaril.Semantics.NondeterministicTrace.Finite.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Silmaril.Isotope.Semantics (BoundEnv)
open Region (packedExitType)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Reply (Γ₀ run traceArrow traceArrow_eq_iff_run traceArrow_of_valid valid_of_equiv
  bind_eq_iff_for_replies run_prefix_determined PrefixDetermined)
open LetSeq.StraightLine.Structural (Shape Slot Assembly Separates Event Log Trace model)
open Silmaril.Semantics.NondeterministicTrace (Finite)
open scoped LetSeq.StraightLine.Structural Tagged

set_option backward.isDefEq.respectTransparency false

local notation "Value" => LetSeq.StraightLine.Structural.Value

variable {α Φ : Type} [TaggedSignature α Φ] {n : Nat} {β : BoundCtx (Ty α) n}

private theorem run_slot {A : Ty α} (s : Slot β A) (ρ : BoundEnv Value β) :
    run (slotTyping (Φ := Φ) s) ρ = pure (s.value ρ) := by
  have evaluation (B : Ty α) (e : β.get s.1 = B) :
      run (cast (congrArg (Derivation Φ Γ₀ β (.bv s.1)) e) .bv) ρ =
        pure (cast (congrArg Value e) (ρ s.1)) := by
    cases e
    rfl
  exact evaluation A s.2

private theorem run_arg {A : Ty α} (v : Assembly β A) (ρ : BoundEnv Value β) :
    run (argTyping (Φ := Φ) v) ρ = pure (v.value ρ) := by
  induction v with
  | atom s => exact run_slot s ρ
  | unit => rfl
  | pair a b iha ihb =>
    unfold run at iha ihb
    simp only [run, argTyping, Assembly.value, Derivation.denote, iha, ihb, pure_bind]
    rfl

private theorem arg_inj {A : Ty α} {ρ : BoundEnv Value β} {used : Set Nat} (sep : Separates ρ used) :
    Function.Injective (Assembly.value (A := A) ρ) := by
  intro p
  induction p with
  | @atom a s =>
    intro q h
    cases q with
    | atom t => exact congrArg Assembly.atom (sep.injective a h)
  | unit =>
    intro q _
    cases q
    rfl
  | pair a b iha ihb =>
    intro q h
    cases q with
    | pair x y => exact congrArg₂ Assembly.pair (iha (Prod.mk.inj h).1) (ihb (Prod.mk.inj h).2)

private theorem run_exit {L : List (Ty α)} {A : Ty α} (exit : ExitAt L A)
    {t : LetCase.LocallyNameless.Tm Empty Φ n} (d : Derivation Φ Γ₀ β t A) (ρ : BoundEnv Value β)
    (x : Value A) (h : run d ρ = pure x) : run (exit.typing d) ρ = pure (exit.value x) := by
  induction exit with
  | here =>
    unfold run at h
    simp only [run, ExitAt.typing, Derivation.denote, h, pure_bind]
    rfl
  | there later ih =>
    have inner := ih d x h
    unfold run at inner
    simp only [run, ExitAt.typing, Derivation.denote, inner, pure_bind]
    rfl

private theorem run_ret {L : List (Ty α)} {A : Ty α} (exit : ExitAt L A) (payload : Assembly β A)
    (ρ : BoundEnv Value β) :
    run (CaseTree.ret (Φ := Φ) exit payload).typing ρ = pure (exit.value (payload.value ρ)) :=
  run_exit exit (argTyping payload) ρ (payload.value ρ) (run_arg payload ρ)

omit [TaggedSignature α Φ] in
/-- The value returned at an exit fixes the exit position, its type and
the payload value. Two exits of the same type are told apart. -/
private theorem exit_value_inj {L : List (Ty α)} {A B : Ty α} (e : ExitAt L A) (e' : ExitAt L B)
    (x : Value A) (y : Value B) (h : e.value x = e'.value y) :
    ∃ same : A = B, same ▸ x = y ∧ ∀ t : LetCase.LocallyNameless.Tm Empty Φ n, e.term t = e'.term t := by
  induction e with
  | here =>
    cases e' with
    | here => exact ⟨rfl, Sum.inl.inj h, fun _ => rfl⟩
    | there later => cases h
  | there later ih =>
    cases e' with
    | here => cases h
    | there later' =>
      obtain ⟨type, payload, terms⟩ := ih later' x (Sum.inr.inj h)
      exact ⟨type, payload, fun t => congrArg LetCase.LocallyNameless.Tm.inr (terms t)⟩

omit [TaggedSignature α Φ] in
/-- The value returned at an exit fixes the type of the exit, the payload
value and the position of the exit among the ordered exits. -/
theorem exit_value_index_proof {L : List (Ty α)} {A B : Ty α} (e : ExitAt L A) (e' : ExitAt L B)
    (x : Value A) (y : Value B) (h : e.value x = e'.value y) :
    ∃ same : A = B, same ▸ x = y ∧ e.index = e'.index := by
  induction e with
  | here =>
    cases e' with
    | here => exact ⟨rfl, Sum.inl.inj h, rfl⟩
    | there later => cases h
  | there later ih =>
    cases e' with
    | here => cases h
    | there later' =>
      obtain ⟨type, payload, position⟩ := ih later' x (Sum.inr.inj h)
      exact ⟨type, payload, congrArg Nat.succ position⟩

/-- A leaf returns the value of its payload at its exit. -/
theorem run_ret_proof {L : List (Ty α)} {A : Ty α} (exit : ExitAt L A) (payload : Assembly β A)
    (ρ : BoundEnv Value β) :
    run (CaseTree.ret (Φ := Φ) exit payload).typing ρ = pure (exit.value (payload.value ρ)) :=
  run_ret exit payload ρ

/-- An assembled payload is determined by its value at an environment that
separates the atom slots. -/
theorem payload_inj_proof {A : Ty α} {ρ : BoundEnv Value β} {used : Set Nat} (sep : Separates ρ used) :
    Function.Injective (Assembly.value (A := A) ρ) :=
  arg_inj sep

/-- Two leaves with the same run at an environment that separates the
atom slots have the same exit position, exit type and payload tree. -/
theorem ret_eq_of_run_proof {L : List (Ty α)} {A B : Ty α} (e : ExitAt L A) (e' : ExitAt L B)
    (p : Assembly β A) (q : Assembly β B) (ρ : BoundEnv Value β) {used : Set Nat} (sep : Separates ρ used)
    (same : run (CaseTree.ret (Φ := Φ) e p).typing ρ = run (CaseTree.ret (Φ := Φ) e' q).typing ρ) :
    ∃ type : A = B, type ▸ p = q ∧ e.index = e'.index := by
  rw [run_ret, run_ret] at same
  have mem : (e.value (p.value ρ), (1 : Log α Φ)) ∈ Finite.outcomes (pure (e.value (p.value ρ))) := rfl
  rw [same] at mem
  have values : (e.value (p.value ρ), (1 : Log α Φ)) = (e'.value (q.value ρ), 1) := mem
  obtain ⟨rfl, value, position⟩ := exit_value_index_proof e e' _ _ (Prod.mk.inj values).1
  exact ⟨rfl, arg_inj sep value, position⟩

/-- The continuation of a request node on a tagged reply. -/
private def arms {L : List (Ty α)} (f : Φ) {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (left : CaseTree (β.snoc (.base (TaggedSignature.left f))) L l)
    (right : CaseTree (β.snoc (.base (TaggedSignature.right f))) L r) (ρ : BoundEnv Value β) :
    Value (instrTrg (τ := Ty α) f) → Trace α Φ (Value (packedExitType L))
  | .inl x => run left.typing (ρ.snoc x)
  | .inr y => run right.typing (ρ.snoc y)

private theorem run_ask {L : List (Ty α)} (f : Φ) (argument : Assembly β (instrSrc f))
    {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (left : CaseTree (β.snoc (.base (TaggedSignature.left f))) L l)
    (right : CaseTree (β.snoc (.base (TaggedSignature.right f))) L r) (ρ : BoundEnv Value β) :
    run (CaseTree.ask f argument left right).typing ρ =
      (model (α := α)).eval f (argument.value ρ) >>= arms f left right ρ := by
  have h := run_arg (Φ := Φ) argument ρ
  unfold run at h
  simp only [run, CaseTree.typing, Derivation.denote, h, pure_bind]
  congr 1
  funext x
  cases x <;> rfl

private theorem mem_ask {A : Type} {f : Φ} {x : Value (instrSrc (τ := Ty α) f)}
    {k : Value (instrTrg (τ := Ty α) f) → Trace α Φ A} {z : A} {w : Log α Φ} :
    (z, w) ∈ (((model (α := α)).eval f x) >>= k).outcomes ↔
      ∃ reply tail, (z, tail) ∈ (k reply).outcomes ∧ FreeMonoid.of ⟨f, x, reply⟩ * tail = w := by
  rw [Finite.mem_bind]
  constructor
  · rintro ⟨y, u, v, ⟨reply, hr⟩, hv, rfl⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    exact ⟨reply, v, hv, rfl⟩
  · rintro ⟨reply, tail, hv, rfl⟩
    exact ⟨reply, _, tail, ⟨reply, rfl⟩, hv, rfl⟩

private theorem log_cons_inj {e f : Event (α := α) (Φ := Φ)} {l r : Log α Φ}
    (h : FreeMonoid.of e * l = FreeMonoid.of f * r) : e = f ∧ l = r := by
  have words : e :: l.toList = f :: r.toList := congrArg FreeMonoid.toList h
  exact ⟨(List.cons.inj words).1, FreeMonoid.ext (List.cons.inj words).2⟩

private theorem log_cons_ne_one (e : Event (α := α) (Φ := Φ)) (l : Log α Φ) : FreeMonoid.of e * l ≠ 1 := by
  intro h
  have words : e :: l.toList = [] := congrArg FreeMonoid.toList h
  cases words

private theorem value_zero {a b : α} (ρ : BoundEnv Value β) (x : Nat)
    (h : (β.snoc (.base a)).get 0 = .base b) :
    Slot.value (⟨0, h⟩ : Slot (β.snoc (.base a)) (.base b)) (ρ.snoc (A := Ty.base a) x) = x := by
  cases (Ty.base.inj h : a = b)
  rfl

private theorem separates_fresh {ρ : BoundEnv Value β} {k : Nat} (sep : Separates ρ (Set.Iio k)) (a : α) :
    Separates (ρ.snoc (A := Ty.base a) (k : Nat)) (Set.Iio (k + 1)) where
  injective b := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    revert hi hj
    refine Fin.cases (fun hi => ?_) (fun i hi => ?_) i
    · refine Fin.cases (fun hj _ => rfl) (fun j hj eq => ?_) j
      have same : k = Slot.value (⟨j, hj⟩ : Slot β (.base b)) ρ := (value_zero ρ k hi).symm.trans eq
      exact (Nat.lt_irrefl k (same ▸ sep.allocated b ⟨j, hj⟩)).elim
    · refine Fin.cases (fun hj eq => ?_) (fun j hj eq => ?_) j
      · have same : k = Slot.value (⟨i, hi⟩ : Slot β (.base b)) ρ := (value_zero ρ k hj).symm.trans eq.symm
        exact (Nat.lt_irrefl k (same ▸ sep.allocated b ⟨i, hi⟩)).elim
      · have same := sep.injective b (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) eq
        exact Subtype.ext (congrArg Fin.succ (congrArg Subtype.val same))
  allocated b := by
    rintro ⟨i, hi⟩
    revert hi
    refine Fin.cases (fun hi => ?_) (fun j hj => ?_) i
    · exact (value_zero ρ k hi).symm ▸ Nat.lt_succ_self k
    · exact Nat.lt_succ_of_lt (sep.allocated b ⟨j, hj⟩)

/-- A separating environment extends by a fresh token at a new atom slot. -/
theorem separates_fresh_proof {ρ : BoundEnv Value β} {k : Nat} (sep : Separates ρ (Set.Iio k)) (a : α) :
    Separates (ρ.snoc (A := Ty.base a) (k : Nat)) (Set.Iio (k + 1)) :=
  separates_fresh sep a

/-- A context of atom slots is separable. -/
theorem separable_atoms_proof {β : BoundCtx (Ty α) n} (atoms : AtomContext β) : Separable β := by
  induction atoms with
  | nil => exact ⟨fun i => i.elim0, 0, ⟨fun _ i => i.1.elim0, fun _ i => i.1.elim0⟩⟩
  | snoc older a ih =>
    obtain ⟨ρ, k, sep⟩ := ih
    exact ⟨ρ.snoc (A := Ty.base a) (k : Nat), k + 1, separates_fresh sep a⟩

private theorem tree_nonempty {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree β L t) :
    ∀ ρ : BoundEnv Value β, (run tree.typing ρ).outcomes.Nonempty := by
  induction tree with
  | ret s =>
    intro ρ
    rw [run_ret]
    exact ⟨(_, 1), rfl⟩
  | ask f argument left right ihl ihr =>
    intro ρ
    rw [run_ask]
    obtain ⟨⟨z, w⟩, h⟩ := ihl (ρ.snoc (A := Ty.base (TaggedSignature.left f)) (0 : Nat))
    exact ⟨(z, _), mem_ask.mpr ⟨.inl (0 : Nat), w, h, rfl⟩⟩

private theorem arms_eq_iff {L : List (Ty α)} (f : Φ) (argument : Assembly β (instrSrc f))
    {l r l' r' : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (left : CaseTree (β.snoc (.base (TaggedSignature.left f))) L l)
    (right : CaseTree (β.snoc (.base (TaggedSignature.right f))) L r)
    (left' : CaseTree (β.snoc (.base (TaggedSignature.left f))) L l')
    (right' : CaseTree (β.snoc (.base (TaggedSignature.right f))) L r') (ρ : BoundEnv Value β) :
    ((model (α := α)).eval f (argument.value ρ) >>= arms f left right ρ) =
        ((model (α := α)).eval f (argument.value ρ) >>= arms f left' right' ρ) ↔
      (∀ x : Nat, run left.typing (ρ.snoc (A := Ty.base (TaggedSignature.left f)) x) =
        run left'.typing (ρ.snoc (A := Ty.base (TaggedSignature.left f)) x)) ∧
      (∀ y : Nat, run right.typing (ρ.snoc (A := Ty.base (TaggedSignature.right f)) y) =
        run right'.typing (ρ.snoc (A := Ty.base (TaggedSignature.right f)) y)) := by
  have determined : PrefixDetermined ((model (α := α)).eval f (argument.value ρ)) := by
    have pd : PrefixDetermined (run (Derivation.op (f := f) (argTyping (Φ := Φ) argument)) ρ) :=
      run_prefix_determined _ ρ
    have evaluated : run (Derivation.op (f := f) (argTyping (Φ := Φ) argument)) ρ =
        (model (α := α)).eval f (argument.value ρ) := by
      have value := run_arg (Φ := Φ) argument ρ
      unfold run at value
      simp only [run, Derivation.denote, value, pure_bind]
    rwa [evaluated] at pd
  rw [bind_eq_iff_for_replies determined]
  constructor
  · intro agree
    exact ⟨fun x => agree (.inl x) _ ⟨.inl x, rfl⟩, fun y => agree (.inr y) _ ⟨.inr y, rfl⟩⟩
  · rintro ⟨hl, hr⟩ reply w -
    cases reply with
    | inl x => exact hl x
    | inr y => exact hr y

/-- At a request node with the same primitive and argument, the runs agree
exactly when the arms agree at every payload token. -/
theorem ask_run_eq_iff_proof {L : List (Ty α)} (f : Φ) (argument : Assembly β (instrSrc f))
    {l r l' r' : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (left : CaseTree (β.snoc (.base (TaggedSignature.left f))) L l)
    (right : CaseTree (β.snoc (.base (TaggedSignature.right f))) L r)
    (left' : CaseTree (β.snoc (.base (TaggedSignature.left f))) L l')
    (right' : CaseTree (β.snoc (.base (TaggedSignature.right f))) L r') (ρ : BoundEnv Value β) :
    run (CaseTree.ask f argument left right).typing ρ = run (CaseTree.ask f argument left' right').typing ρ ↔
      (∀ x : Nat, run left.typing (ρ.snoc (A := Ty.base (TaggedSignature.left f)) x) =
        run left'.typing (ρ.snoc (A := Ty.base (TaggedSignature.left f)) x)) ∧
      (∀ y : Nat, run right.typing (ρ.snoc (A := Ty.base (TaggedSignature.right f)) y) =
        run right'.typing (ρ.snoc (A := Ty.base (TaggedSignature.right f)) y)) := by
  rw [run_ask, run_ask]
  exact arms_eq_iff f argument left right left' right' ρ

/-- Two case trees with the same run at an environment that separates the
atom slots are the same term. A request node allocates the next token as
the payload of both tags. -/
theorem caseTree_eq_of_run_proof {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ n} (p : CaseTree β L t) :
    ∀ {u : LetCase.LocallyNameless.Tm Empty Φ n} (q : CaseTree β L u) (ρ : BoundEnv Value β) (k : Nat),
      Separates ρ (Set.Iio k) → run p.typing ρ = run q.typing ρ → t = u := by
  induction p with
  | @ret _ β L A exit s =>
    intro u q ρ k sep h
    have mem : (exit.value (s.value ρ), (1 : Log α Φ)) ∈
        Finite.outcomes (pure (exit.value (s.value ρ))) := rfl
    rw [← run_ret (Φ := Φ), h] at mem
    cases q with
    | ret exit' s' =>
      rw [run_ret] at mem
      have same : (exit.value (s.value ρ), (1 : Log α Φ)) = (exit'.value (s'.value ρ), 1) := mem
      obtain ⟨rfl, value, terms⟩ := exit_value_inj (Φ := Φ) exit exit' _ _ (Prod.mk.inj same).1
      cases arg_inj sep value
      exact terms _
    | ask g b left right =>
      rw [run_ask] at mem
      obtain ⟨reply, tail, -, log⟩ := mem_ask.mp mem
      exact (log_cons_ne_one _ _ log).elim
  | @ask _ β L f argument l r left right ihl ihr =>
    intro u q ρ k sep h
    cases q with
    | ret exit' s' =>
      have mem : (exit'.value (s'.value ρ), (1 : Log α Φ)) ∈
          Finite.outcomes (pure (exit'.value (s'.value ρ))) := rfl
      rw [← run_ret (Φ := Φ), ← h, run_ask] at mem
      obtain ⟨reply, tail, -, log⟩ := mem_ask.mp mem
      exact (log_cons_ne_one _ _ log).elim
    | ask g b left' right' =>
      rw [run_ask, run_ask] at h
      obtain ⟨⟨z, w⟩, hz⟩ := tree_nonempty left (ρ.snoc (A := Ty.base (TaggedSignature.left f)) (k : Nat))
      have mem : (z, FreeMonoid.of ⟨f, argument.value ρ, .inl (k : Nat)⟩ * w) ∈
          ((model (α := α)).eval f (argument.value ρ) >>= arms f left right ρ).outcomes :=
        mem_ask.mpr ⟨.inl (k : Nat), w, hz, rfl⟩
      rw [h] at mem
      obtain ⟨reply, tail, -, log⟩ := mem_ask.mp mem
      have head := (log_cons_inj log).1
      have generator : g = f := congrArg Event.generator head
      subst g
      have fields := Event.mk.inj head
      cases arg_inj sep (eq_of_heq fields.2.1)
      have agree := (arms_eq_iff f argument left right left' right' ρ).mp h
      have hl := ihl left' (ρ.snoc (A := Ty.base (TaggedSignature.left f)) (k : Nat)) (k + 1)
        (separates_fresh sep _) (agree.1 k)
      have hr := ihr right' (ρ.snoc (A := Ty.base (TaggedSignature.right f)) (k : Nat)) (k + 1)
        (separates_fresh sep _) (agree.2 k)
      rw [hl, hr]

/-- The ordered trace interpretation with atoms reflects native equality
of branching operands over a separable bound context. -/
theorem branching_reflects_proof {L : List (Ty α)} (x y : Operand Φ β (packedExitType L))
    (hx : Branching x) (hy : Branching y) (separable : Separable β)
    (same : traceArrow x.2 = traceArrow y.2) :
    Equiv false Γ₀ β x.1 y.1 (packedExitType L) := by
  obtain ⟨t, p, et⟩ := hx
  obtain ⟨u, q, eu⟩ := hy
  obtain ⟨ρ, k, sep⟩ := separable
  have left : traceArrow x.2 = traceArrow p.typing := traceArrow_of_valid (valid_of_equiv x.2 p.typing et)
  have right : traceArrow y.2 = traceArrow q.typing := traceArrow_of_valid (valid_of_equiv y.2 q.typing eu)
  have runs := (traceArrow_eq_iff_run p.typing q.typing).mp (left.symm.trans (same.trans right)) ρ
  cases caseTree_eq_of_run_proof p q ρ k sep runs
  exact et.trans eu.symm

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
