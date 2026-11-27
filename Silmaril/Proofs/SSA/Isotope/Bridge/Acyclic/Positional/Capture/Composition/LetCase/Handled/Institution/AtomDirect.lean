module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Region (packedExitType)
open LetCase.LocallyNameless (Derivation Equiv HasType Pure)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Slot Assembly)
open scoped LetSeq.StraightLine.Structural Tagged Binary

variable {α Φ : Type} {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}

/-! ## Renaming of exits and payloads -/

/-- Renaming commutes with returning at an exit. -/
theorem exit_term_rename_proof {A : Ty α} (e : ExitAt L A) {m : Nat} (ξ : Fin n → Fin m)
    (t : LetCase.LocallyNameless.Tm Empty Φ n) : (e.term t).rename ξ = e.term (t.rename ξ) := by
  induction e with
  | here => rfl
  | there later ih => exact congrArg LetCase.LocallyNameless.Tm.inr ih

/-- Renaming commutes with assembling a payload. -/
theorem argTerm_rename_proof {A : Ty α} (p : Assembly β A) {m : Nat} {γ : BoundCtx (Ty α) m}
    (ρ : BoundCtx.Renaming β γ) :
    (argTerm (Φ := Φ) p).rename ρ.toFun = argTerm (p.rename ρ) := by
  induction p with
  | atom s => rfl
  | unit => rfl
  | pair a b iha ihb => exact congrArg₂ LetCase.LocallyNameless.Tm.pair iha ihb

/-! ## A pair slot commutes with a later binding

A pattern let on a pair slot may be moved in front of a let that precedes
it. The pair slot is a variable, so it is pure. The derivation uses native
typed laws only: pure-let beta at the slot and at a pair of variables,
pair eta at the slot, the sequencing law that pulls a pattern let out of
the scrutinee of a let, and pair beta. -/

section Commute

variable [HasTy Φ (Ty α)]

/-- A let followed by a pattern let on an older pair slot is natively
equal to the pattern let followed by the let. The bound term is weakened
past the two components, and the body has its three newest slots moved. -/
theorem let_pair_comm_proof {m : Nat} {Δ : BoundCtx (Ty α) m} {A B X C : Ty α} (j : Fin m)
    (hj : Δ.get j = .product A B) {E : LetCase.LocallyNameless.Tm Empty Φ m} {body : LetCase.LocallyNameless.Tm Empty Φ (m + 3)}
    (hE : HasType Φ Γ₀ Δ E X) (hBody : HasType Φ Γ₀ (((Δ.snoc X).snoc A).snoc B) body C) :
    Equiv false Γ₀ Δ (.let₁ E (.let₂ (.bv j.succ) body))
      (.let₂ (.bv j) (.let₁ (E.rename (fun i => i.succ.succ)) (body.rename afterPair))) C := by
  have hx : HasType Φ Γ₀ Δ (.bv j) (.product A B) := hj ▸ .bv
  -- the body under the pair slot
  let ins := (((BoundCtx.Renaming.succ Δ (.product A B)).up X).up A).up B
  let K : LetCase.LocallyNameless.Tm Empty Φ (m + 1) := .let₁ (E.rename Fin.succ) (.let₂ (.bv 1) (body.rename ins.toFun))
  have hK : HasType Φ Γ₀ (Δ.snoc (.product A B)) K C :=
    .let₁ (HasType.rename (BoundCtx.Renaming.succ Δ (.product A B)) hE)
      (.let₂ (.bv (ι := (1 : Fin (m + 2)))) (HasType.rename ins hBody))
  have enter := Equiv.letBeta (pureEff := false) Pure.bv hx hK
  have inst_eq : LetCase.LocallyNameless.Tm.instantiate K (.bv j) = .let₁ E (.let₂ (.bv j.succ) body) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst,
      LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    · exact (LetCase.LocallyNameless.Tm.bsubst_congr (fun _ => rfl) E).trans
        (LetCase.LocallyNameless.Tm.bsubst_id E)
    · congr 1
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) body).trans
        (LetCase.LocallyNameless.Tm.bsubst_id body)
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
  rw [inst_eq] at enter
  -- eta-expand the pair slot and pull the pattern let out
  have eta := Equiv.let₁ (Equiv.pairEta (pureEff := false) hx).symm (.refl hK)
  have pull := Equiv.bindLetPair (pureEff := false) hx
    (.pair (.bv (ι := (1 : Fin (m + 2)))) (.bv (ι := (0 : Fin (m + 2))))) hK
  -- substitute the pair of components for the pair slot
  have hPair : HasType Φ Γ₀ ((Δ.snoc A).snoc B) (.pair (.bv 1) (.bv 0)) (.product A B) :=
    .pair (.bv (ι := (1 : Fin (m + 2)))) (.bv (ι := (0 : Fin (m + 2))))
  have beta := Equiv.letBeta (pureEff := false) (Pure.pair Pure.bv Pure.bv) hPair hK.underBinder.underBinder
  let past : BoundCtx.Renaming Δ ((Δ.snoc A).snoc B) :=
    (BoundCtx.Renaming.succ Δ A).comp (BoundCtx.Renaming.succ (Δ.snoc A) B)
  let ins2 := ((past.up X).up A).up B
  have beta_eq : LetCase.LocallyNameless.Tm.instantiate K.underBinder.underBinder (.pair (.bv 1) (.bv 0)) =
      .let₁ (E.rename (fun i => i.succ.succ)) (.let₂ (.pair (.bv 2) (.bv 1)) (body.rename ins2.toFun)) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.underBinder,
      LetCase.LocallyNameless.Tm.rename_comp, LetCase.LocallyNameless.Tm.bsubst,
      LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    · exact (LetCase.LocallyNameless.Tm.bsubst_congr (fun _ => rfl) E).trans
        (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename _ E)
    · congr 1
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) body).trans
        (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename ins2.toFun body)
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
  rw [beta_eq] at beta
  -- reduce the pattern let on the pair of components
  have hBody₂ : HasType Φ Γ₀ (((((Δ.snoc A).snoc B).snoc X).snoc A).snoc B) (body.rename ins2.toFun) C :=
    HasType.rename ins2 hBody
  have hA : HasType Φ Γ₀ (((Δ.snoc A).snoc B).snoc X) (.bv 2) A := .bv (ι := (2 : Fin (m + 3)))
  have hB : HasType Φ Γ₀ (((Δ.snoc A).snoc B).snoc X) (.bv 1) B := .bv (ι := (1 : Fin (m + 3)))
  have split := Equiv.pairBeta (pureEff := false) hA hB hBody₂
  have first := Equiv.letBeta (pureEff := false) Pure.bv hA (.let₁ hB.lift hBody₂)
  have first_eq : LetCase.LocallyNameless.Tm.instantiate
      (.let₁ (LetCase.LocallyNameless.Tm.lift (.bv 1)) (body.rename ins2.toFun))
      (.bv (2 : Fin (m + 3))) =
      .let₁ (.bv 1) (LetCase.LocallyNameless.Tm.bsubst
        (LetCase.LocallyNameless.Tm.upSub (Fin.cases (.bv 2) (fun i => .bv i))) (body.rename ins2.toFun)) := rfl
  rw [first_eq] at first
  obtain ⟨-, typed⟩ := first.hasType
  cases typed with
  | let₁ hV hZ =>
    cases hV
    have second := Equiv.letBeta (pureEff := false) Pure.bv hB hZ
    have second_eq : LetCase.LocallyNameless.Tm.instantiate
        (LetCase.LocallyNameless.Tm.bsubst
          (LetCase.LocallyNameless.Tm.upSub (Fin.cases (.bv 2) (fun i => .bv i))) (body.rename ins2.toFun))
        (.bv (1 : Fin (m + 3))) = body.rename afterPair := by
      simp only [LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst_rename,
        LetCase.LocallyNameless.Tm.bsubst_comp]
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) body).trans
        (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename afterPair body)
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
    rw [second_eq] at second
    have hE'' : HasType Φ Γ₀ ((Δ.snoc A).snoc B) (E.rename (fun i => i.succ.succ)) X :=
      HasType.rename past hE
    exact enter.symm.trans (eta.trans (pull.trans (Equiv.let₂ (.refl hx)
      (beta.trans (Equiv.let₁ (.refl hE'') (split.trans (first.trans second)))))))

end Commute

/-! ## A pair held across a chain of requests

The chain with its final destructuring removed, as a term in which the
slots of the chain and the two components are placed by one renaming. -/

section Chain

variable [TaggedSignature α Φ]

mutual

/-- The chain with its final destructuring removed, as a term. One
renaming places the slots of the chain and the two components. -/
def flatDelay : {a b : α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} → {s : Slot Δ (tupleTy [a, b])} →
    {t : LetCase.LocallyNameless.Tm Empty Φ m} → SpelledDelay a b Δ s L t → {k : Nat} →
    (Fin (m + 1 + 1) → Fin k) → LetCase.LocallyNameless.Tm Empty Φ k
  | _, _, _, _, _, _, .unpack (t := body) _, _, σ => body.rename σ
  | _, _, _, _, _, _, .ask g argument reply, _, σ =>
    flatDelayed reply σ (.op g ((argTerm argument).rename (fun i => σ i.succ.succ)))

/-- The same for the reply of a request, given the renamed request. -/
def flatDelayed : {a b : α} → {tags : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy [a, b])} → {e t : LetCase.LocallyNameless.Tm Empty Φ m} →
    SpelledDelayed a b tags e Δ s L t → {k : Nat} → (Fin (m + 1 + 1) → Fin k) →
    LetCase.LocallyNameless.Tm Empty Φ k → LetCase.LocallyNameless.Tm Empty Φ k
  | _, _, _, _, _, _, _, _, .atom _ next, _, σ, e' =>
    .let₁ e' (flatDelay next (fun i => LetCase.LocallyNameless.Tm.up σ (afterPair i)))
  | _, _, _, _, _, _, _, _, .unit next, _, σ, e' =>
    .let₁ e' (flatDelay next (fun i => LetCase.LocallyNameless.Tm.up σ (afterPair i)))

end

mutual

/-- The flattened chain commutes with renaming. -/
theorem flatDelay_rename : {a b : α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy [a, b])} → {t : LetCase.LocallyNameless.Tm Empty Φ m} →
    (d : SpelledDelay a b Δ s L t) → {k j : Nat} → (σ : Fin (m + 1 + 1) → Fin k) → (π : Fin k → Fin j) →
    (flatDelay d σ).rename π = flatDelay d (fun i => π (σ i))
  | _, _, _, _, _, _, .unpack _, _, _, σ, π => LetCase.LocallyNameless.Tm.rename_comp σ π _
  | _, _, _, _, _, _, .ask g argument reply, _, _, σ, π => by
    have h := flatDelayed_rename reply σ π (.op g ((argTerm argument).rename (fun i => σ i.succ.succ)))
    simpa only [flatDelay, LetCase.LocallyNameless.Tm.rename, LetCase.LocallyNameless.Tm.rename_comp] using h

/-- The same for the reply of a request. -/
theorem flatDelayed_rename : {a b : α} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {s : Slot Δ (tupleTy [a, b])} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ m} → (d : SpelledDelayed a b tags e Δ s L t) → {k j : Nat} →
    (σ : Fin (m + 1 + 1) → Fin k) → (π : Fin k → Fin j) → (e' : LetCase.LocallyNameless.Tm Empty Φ k) →
    (flatDelayed d σ e').rename π = flatDelayed d (fun i => π (σ i)) (e'.rename π)
  | _, _, _, _, _, _, _, _, .atom _ next, _, _, σ, π, e' => by
    have h := flatDelay_rename next (fun i => LetCase.LocallyNameless.Tm.up σ (afterPair i))
      (LetCase.LocallyNameless.Tm.up π)
    have lifted : (fun i => LetCase.LocallyNameless.Tm.up π (LetCase.LocallyNameless.Tm.up σ (afterPair i))) =
        fun i => LetCase.LocallyNameless.Tm.up (fun i => π (σ i)) (afterPair i) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) (afterPair i)
    rw [lifted] at h
    exact congrArg (LetCase.LocallyNameless.Tm.let₁ (e'.rename π)) h
  | _, _, _, _, _, _, _, _, .unit next, _, _, σ, π, e' => by
    have h := flatDelay_rename next (fun i => LetCase.LocallyNameless.Tm.up σ (afterPair i))
      (LetCase.LocallyNameless.Tm.up π)
    have lifted : (fun i => LetCase.LocallyNameless.Tm.up π (LetCase.LocallyNameless.Tm.up σ (afterPair i))) =
        fun i => LetCase.LocallyNameless.Tm.up (fun i => π (σ i)) (afterPair i) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) (afterPair i)
    rw [lifted] at h
    exact congrArg (LetCase.LocallyNameless.Tm.let₁ (e'.rename π)) h

end

mutual

/-- The flattened chain is typed where the two components are slots. -/
theorem flatDelay_typed : {a b : α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy [a, b])} → {t : LetCase.LocallyNameless.Tm Empty Φ m} →
    (d : SpelledDelay a b Δ s L t) → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    (σ : BoundCtx.Renaming ((Δ.snoc (.base a)).snoc (.base b)) Θ) →
    HasType Φ Γ₀ Θ (flatDelay d σ.toFun) (packedExitType L)
  | _, _, _, _, _, _, .unpack body, _, _, σ => HasType.rename σ body.typing.toHasType
  | a, b, _, Δ, _, _, .ask g argument reply, _, _, σ =>
    flatDelayed_typed reply σ _
      (HasType.rename (((BoundCtx.Renaming.succ Δ (.base a)).comp (BoundCtx.Renaming.succ _ (.base b))).comp σ)
        (Derivation.op (f := g) (argTyping argument)).toHasType)

/-- The same for the reply of a request. -/
theorem flatDelayed_typed : {a b : α} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {s : Slot Δ (tupleTy [a, b])} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ m} → (d : SpelledDelayed a b tags e Δ s L t) → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (σ : BoundCtx.Renaming ((Δ.snoc (.base a)).snoc (.base b)) Θ) →
    (e' : LetCase.LocallyNameless.Tm Empty Φ k) → HasType Φ Γ₀ Θ e' (tagsTy tags) →
    HasType Φ Γ₀ Θ (flatDelayed d σ.toFun e') (packedExitType L)
  | _, _, _, _, Δ, _, _, _, .atom _ next, _, _, σ, _, he' =>
    .let₁ he' (flatDelay_typed next ((afterPairRenaming Δ _ _ _).comp (σ.up _)))
  | _, _, _, _, Δ, _, _, _, .unit next, _, _, σ, _, he' =>
    .let₁ he' (flatDelay_typed next ((afterPairRenaming Δ _ _ _).comp (σ.up _)))

end

mutual

/-- A chain with a held pair, renamed, is natively equal to destructuring
the pair first and then running the flattened chain. One commuting step is
used for each request of the chain. -/
theorem delay_comm : {a b : α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy [a, b])} → {t : LetCase.LocallyNameless.Tm Empty Φ m} →
    (d : SpelledDelay a b Δ s L t) → {k : Nat} → {Δ' : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming Δ Δ') →
    Equiv false Γ₀ Δ' (t.rename ρ.toFun)
      (.let₂ (.bv (ρ.toFun s.1))
        (flatDelay d (LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up ρ.toFun))))
      (packedExitType L)
  | _, _, _, _, _, _, .unpack body, _, _, ρ =>
    .refl (HasType.rename ρ (SpelledDelay.unpack body).typing.toHasType)
  | _, _, _, _, _, _, .ask g argument reply, _, _, ρ => by
    have h := delayed_comm reply ρ (HasType.rename ρ (Derivation.op (f := g) (argTyping argument)).toHasType)
    have request : ((LetCase.LocallyNameless.Tm.op g (argTerm (Φ := Φ) argument)).rename ρ.toFun).rename
        (fun i => i.succ.succ) =
        .op g ((argTerm argument).rename (fun i => LetCase.LocallyNameless.Tm.up
          (LetCase.LocallyNameless.Tm.up ρ.toFun) i.succ.succ)) := by
      simp only [LetCase.LocallyNameless.Tm.rename, LetCase.LocallyNameless.Tm.rename_comp]
      rfl
    rw [request] at h
    exact h

/-- The same for the reply of a request, given the typing of the renamed
request. -/
theorem delayed_comm : {a b : α} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {s : Slot Δ (tupleTy [a, b])} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ m} → (d : SpelledDelayed a b tags e Δ s L t) → {k : Nat} →
    {Δ' : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming Δ Δ') →
    HasType Φ Γ₀ Δ' (e.rename ρ.toFun) (tagsTy tags) →
    Equiv false Γ₀ Δ' (t.rename ρ.toFun)
      (.let₂ (.bv (ρ.toFun s.1))
        (flatDelayed d (LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up ρ.toFun))
          ((e.rename ρ.toFun).rename (fun i => i.succ.succ))))
      (packedExitType L)
  | a, b, _, _, _, s, _, _, .atom c next, _, Δ', ρ, he => by
    have ih := delay_comm next (ρ.up (tupleTy [c]))
    have typed := flatDelay_typed next (((ρ.up (tupleTy [c])).up (.base a)).up (.base b))
    have slot : Δ'.get (ρ.toFun s.1) = .product (.base a) (.base b) := (ρ.typed s.1).trans s.2
    have comm := let_pair_comm_proof (ρ.toFun s.1) slot he typed
    have moved : (flatDelay next (((ρ.up (tupleTy [c])).up (.base a)).up (.base b)).toFun).rename afterPair =
        flatDelay next (fun i => LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up
          (LetCase.LocallyNameless.Tm.up ρ.toFun)) (afterPair i)) := by
      rw [flatDelay_rename]
      congr 1
      funext i
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
    rw [moved] at comm
    exact (Equiv.let₁ (.refl he) ih).trans comm
  | a, b, _, _, _, s, _, _, .unit next, _, Δ', ρ, he => by
    have ih := delay_comm next (ρ.up (tupleTy ([] : List α)))
    have typed := flatDelay_typed next (((ρ.up (tupleTy ([] : List α))).up (.base a)).up (.base b))
    have slot : Δ'.get (ρ.toFun s.1) = .product (.base a) (.base b) := (ρ.typed s.1).trans s.2
    have comm := let_pair_comm_proof (ρ.toFun s.1) slot he typed
    have moved : (flatDelay next (((ρ.up (tupleTy ([] : List α))).up (.base a)).up (.base b)).toFun).rename afterPair =
        flatDelay next (fun i => LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up
          (LetCase.LocallyNameless.Tm.up ρ.toFun)) (afterPair i)) := by
      rw [flatDelay_rename]
      congr 1
      funext i
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
    rw [moved] at comm
    exact (Equiv.let₁ (.refl he) ih).trans comm

end

end Chain

/-! ## The native equation between a spelling and its normal form

Each head uses one native sequencing law. A bound head needs none. A pair
head uses the law that binds the scrutinee of a pattern let, and a case
head the law that binds the scrutinee of a case. In both, the body is
weakened past the bound reply. -/

section Spelled

variable [TaggedSignature α Φ]

mutual

theorem Spelled.normal_equiv : {n : Nat} → {β : BoundCtx (Ty α) n} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → (d : Spelled β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → (ρ : BoundCtx.Renaming β γ) →
    Equiv false Γ₀ γ (t.rename ρ.toFun) (d.normal ρ).1 (packedExitType L)
  | _, _, _, .ret exit payload, _, _, ρ => by
    have term : (exit.term (argTerm (Φ := Φ) payload)).rename ρ.toFun =
        exit.term (argTerm (payload.rename ρ)) := by
      rw [exit_term_rename_proof, argTerm_rename_proof]
    rw [term]
    exact .refl (CaseTree.ret exit (payload.rename ρ)).typing.toHasType
  | _, _, _, .ask f argument head, _, γ, ρ => by
    have request : (LetCase.LocallyNameless.Tm.op f (argTerm (Φ := Φ) argument)).rename ρ.toFun =
        .op f (argTerm (argument.rename ρ)) := by
      simp only [LetCase.LocallyNameless.Tm.rename, argTerm_rename_proof]
    have he : HasType Φ Γ₀ γ ((LetCase.LocallyNameless.Tm.op f (argTerm (Φ := Φ) argument)).rename ρ.toFun)
        (tagsTy (replyTags f)) := by
      rw [request]
      exact (Derivation.op (f := f) (argTyping (argument.rename ρ))).toHasType
    have h := head.normal_equiv ρ he
    rw [request] at h
    exact h

theorem SpelledHead.normal_equiv : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ n} → (d : SpelledHead tags e β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → (ρ : BoundCtx.Renaming β γ) →
    HasType Φ Γ₀ γ (e.rename ρ.toFun) (tagsTy tags) →
    Equiv false Γ₀ γ (t.rename ρ.toFun) (.let₁ (e.rename ρ.toFun) (d.normal ρ).1) (packedExitType L)
  | _, _, _, _, _, .bind reply, _, _, ρ, he => Equiv.let₁ (.refl he) (reply.normal_equiv ρ)
  | _, _, _, e, _, .destruct (t := body) a b rest later, _, γ, ρ, he => by
    have typed : HasType Φ Γ₀ ((γ.snoc (.base a)).snoc (tupleTy (b :: rest)))
        (body.rename (LetCase.LocallyNameless.Tm.up (LetCase.LocallyNameless.Tm.up ρ.toFun)))
        (packedExitType L) :=
      HasType.rename ((ρ.up _).up _) later.typing.toHasType
    have bind := Equiv.bindPair (pureEff := false) he typed
    have weaken : (body.rename (LetCase.LocallyNameless.Tm.up
        (LetCase.LocallyNameless.Tm.up ρ.toFun))).underTwoBinders =
          body.rename (LetCase.LocallyNameless.Tm.up
            (armRenaming ρ (tupleTy (a :: b :: rest)) (.base a)).toFun) := by
      rw [LetCase.LocallyNameless.Tm.underTwoBinders, LetCase.LocallyNameless.Tm.rename_comp]
      apply LetCase.LocallyNameless.Tm.rename_congr
      intro i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
    rw [weaken] at bind
    exact bind.trans (Equiv.let₁ (.refl he) (Equiv.let₂ (.refl .bv) (later.normal_equiv (armRenaming ρ _ _))))
  | _, _, _, e, _, .branch (l := l) (r := r) atoms next rest left right, _, γ, ρ, he => by
    have hl : HasType Φ Γ₀ (γ.snoc (tupleTy atoms)) (l.rename (LetCase.LocallyNameless.Tm.up ρ.toFun))
        (packedExitType L) :=
      HasType.rename (ρ.up _) left.typing.toHasType
    have hr : HasType Φ Γ₀ (γ.snoc (tagsTy (next :: rest))) (r.rename (LetCase.LocallyNameless.Tm.up ρ.toFun))
        (packedExitType L) :=
      HasType.rename (ρ.up _) right.typing.toHasType
    have bind := Equiv.bindCase (pureEff := false) he hl hr
    have weaken (a : LetCase.LocallyNameless.Tm Empty Φ (_ + 1)) :
        (a.rename (LetCase.LocallyNameless.Tm.up ρ.toFun)).underBinder =
          a.rename (LetCase.LocallyNameless.Tm.up
            (ρ.comp (BoundCtx.Renaming.succ γ (tagsTy (atoms :: next :: rest)))).toFun) := by
      rw [LetCase.LocallyNameless.Tm.underBinder, LetCase.LocallyNameless.Tm.rename_comp]
      apply LetCase.LocallyNameless.Tm.rename_congr
      intro i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [weaken, weaken] at bind
    exact bind.trans (Equiv.let₁ (.refl he) (Equiv.case (.refl .bv)
      (left.normal_equiv (ρ.comp (BoundCtx.Renaming.succ γ _)))
      (right.normal_equiv (ρ.comp (BoundCtx.Renaming.succ γ _)))))

theorem SpelledTags.normal_equiv : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → (d : SpelledTags tags β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → (ρ : BoundCtx.Renaming β γ) →
    Equiv false Γ₀ (γ.snoc (tagsTy tags)) (t.rename (LetCase.LocallyNameless.Tm.up ρ.toFun)) (d.normal ρ).1
      (packedExitType L)
  | _, _, _, _, .only _ payload, _, _, ρ => payload.normal_equiv ρ
  | _, _, _, _, .split _ _ _ left right, _, _, ρ =>
    Equiv.case (.refl .bv) (left.normal_equiv (ρ.up _)) (right.normal_equiv (ρ.up _))

theorem SpelledTuple.normal_equiv : {n : Nat} → {β : BoundCtx (Ty α) n} → {atoms : List α} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → (d : SpelledTuple atoms β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → (ρ : BoundCtx.Renaming β γ) →
    Equiv false Γ₀ (γ.snoc (tupleTy atoms)) (t.rename (LetCase.LocallyNameless.Tm.up ρ.toFun)) (d.normal ρ).1
      (packedExitType L)
  | _, _, _, _, .unit body, _, _, ρ => body.normal_equiv (ρ.up _)
  | _, _, _, _, .atom _ body, _, _, ρ => body.normal_equiv (ρ.up _)
  | _, _, _, _, .pair _ _ _ later, _, _, ρ =>
    Equiv.let₂ (.refl .bv) (later.normal_equiv ((ρ.up _).up _))
  | _, _, _, _, .hold _ _ delay, _, _, ρ =>
    (delay_comm delay (ρ.up _)).trans
      (Equiv.let₂ (.refl .bv) (delay.normal_flat (((ρ.up _).up _).up _)))

/-- The flattened chain is natively equal to the normal form of the chain. -/
theorem SpelledDelay.normal_flat : {a b : α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy [a, b])} → {t : LetCase.LocallyNameless.Tm Empty Φ m} →
    (d : SpelledDelay a b Δ s L t) → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    (σ : BoundCtx.Renaming ((Δ.snoc (.base a)).snoc (.base b)) Θ) →
    Equiv false Γ₀ Θ (flatDelay d σ.toFun) (d.normal σ).1 (packedExitType L)
  | _, _, _, _, _, _, .unpack body, _, _, σ => body.normal_equiv σ
  | a, b, _, Δ, _, _, .ask g argument reply, _, Θ, σ => by
    let past : BoundCtx.Renaming Δ Θ :=
      ((BoundCtx.Renaming.succ Δ (.base a)).comp (BoundCtx.Renaming.succ (Δ.snoc (.base a)) (.base b))).comp σ
    have request : LetCase.LocallyNameless.Tm.op g ((argTerm (Φ := Φ) argument).rename
        (fun i => σ.toFun i.succ.succ)) = .op g (argTerm (argument.rename past)) :=
      congrArg (LetCase.LocallyNameless.Tm.op g) (argTerm_rename_proof argument past)
    have h := reply.normal_flat σ _ (Derivation.op (f := g) (argTyping (argument.rename past))).toHasType
    show Equiv false Γ₀ Θ (flatDelayed reply σ.toFun
      (.op g ((argTerm argument).rename (fun i => σ.toFun i.succ.succ)))) _ _
    rw [request]
    exact h

/-- The same for the reply of a request. -/
theorem SpelledDelayed.normal_flat : {a b : α} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {s : Slot Δ (tupleTy [a, b])} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ m} → (d : SpelledDelayed a b tags e Δ s L t) → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (σ : BoundCtx.Renaming ((Δ.snoc (.base a)).snoc (.base b)) Θ) →
    (e' : LetCase.LocallyNameless.Tm Empty Φ k) → HasType Φ Γ₀ Θ e' (tagsTy tags) →
    Equiv false Γ₀ Θ (flatDelayed d σ.toFun e') (.let₁ e' (d.normal σ).1) (packedExitType L)
  | _, _, _, _, Δ, _, _, _, .atom _ next, _, _, σ, _, he' =>
    Equiv.let₁ (.refl he') (next.normal_flat ((afterPairRenaming Δ _ _ _).comp (σ.up _)))
  | _, _, _, _, Δ, _, _, _, .unit next, _, _, σ, _, he' =>
    Equiv.let₁ (.refl he') (next.normal_flat ((afterPairRenaming Δ _ _ _).comp (σ.up _)))

end

end Spelled

section Binary

variable [BinarySignature α Φ]

/-- A direct case tree, renamed, is natively equal to its normal form. This
is the equation of its spelled tree. -/
theorem normal_equiv_proof {t : LetCase.LocallyNameless.Tm Empty Φ n} (d : DirectTree β L t) {m : Nat}
    {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ) :
    Equiv false Γ₀ γ (t.rename ρ.toFun) (d.normal ρ).1 (packedExitType L) :=
  d.spelled.normal_equiv ρ

/-! ## The normal form determines the direct tree -/

omit [BinarySignature α Φ] in
private theorem exit_term_inj {A B : Ty α} (e : ExitAt L A) (e' : ExitAt L B) {m : Nat}
    (t t' : LetCase.LocallyNameless.Tm Empty Φ m) (h : e.term t = e'.term t') :
    t = t' ∧ ∀ {k : Nat} (s : LetCase.LocallyNameless.Tm Empty Φ k), e.term s = e'.term s := by
  induction e with
  | here =>
    cases e' with
    | here => exact ⟨LetCase.LocallyNameless.Tm.inl.inj h, fun _ => rfl⟩
    | there later => cases h
  | there later ih =>
    cases e' with
    | here => cases h
    | there later' =>
      obtain ⟨terms, exits⟩ := ih later' (LetCase.LocallyNameless.Tm.inr.inj h)
      exact ⟨terms, fun s => congrArg LetCase.LocallyNameless.Tm.inr (exits s)⟩

omit [BinarySignature α Φ] in
private theorem payload_rename_inj {A B : Ty α} (p : Assembly β A) (q : Assembly β B) {m : Nat}
    {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ) (inj : Function.Injective ρ.toFun)
    (h : argTerm (Φ := Φ) (p.rename ρ) = argTerm (q.rename ρ)) : argTerm (Φ := Φ) p = argTerm q := by
  induction p generalizing B with
  | atom s =>
    cases q with
    | atom s' => exact congrArg LetCase.LocallyNameless.Tm.bv (inj (LetCase.LocallyNameless.Tm.bv.inj h))
    | unit => cases h
    | pair x y => cases h
  | unit =>
    cases q with
    | atom s' => cases h
    | unit => rfl
    | pair x y => cases h
  | pair a b iha ihb =>
    cases q with
    | atom s' => cases h
    | unit => cases h
    | pair x y =>
      have parts := LetCase.LocallyNameless.Tm.pair.inj h
      exact congrArg₂ LetCase.LocallyNameless.Tm.pair (iha x parts.1) (ihb y parts.2)

omit [BinarySignature α Φ] in
private theorem arm_injective {m : Nat} {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ)
    (inj : Function.Injective ρ.toFun) (reply payload : Ty α) :
    Function.Injective (armRenaming ρ reply payload).toFun := by
  intro i j
  refine Fin.cases (fun h => ?_) (fun i h => ?_) i
  · revert h
    refine Fin.cases (fun _ => rfl) (fun j h => ?_) j
    exact absurd (congrArg Fin.val h) (by simp [armRenaming, BoundCtx.Renaming.up, BoundCtx.Renaming.comp,
      BoundCtx.Renaming.succ])
  · revert h
    refine Fin.cases (fun h => ?_) (fun j h => ?_) j
    · exact absurd (congrArg Fin.val h) (by simp [armRenaming, BoundCtx.Renaming.up, BoundCtx.Renaming.comp,
        BoundCtx.Renaming.succ])
    · have inner : (ρ.toFun i).succ = (ρ.toFun j).succ := Fin.succ_injective _ h
      exact congrArg Fin.succ (inj (Fin.succ_injective _ inner))

/-- Two direct case trees with the same normal form along an injective
renaming are the same term. -/
theorem normal_injective_proof {t : LetCase.LocallyNameless.Tm Empty Φ n} (p : DirectTree β L t) :
    ∀ {u : LetCase.LocallyNameless.Tm Empty Φ n} (q : DirectTree β L u) {m : Nat}
      {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ), Function.Injective ρ.toFun →
      (p.normal ρ).1 = (q.normal ρ).1 → t = u := by
  induction p with
  | @ret _ β L A exit payload =>
    intro u q m γ ρ inj h
    cases q with
    | ret exit' payload' =>
      obtain ⟨terms, exits⟩ := exit_term_inj exit exit' _ _ h
      rw [payload_rename_inj payload payload' ρ inj terms]
      exact exits _
    | ask g b left' right' => cases exit <;> cases h
  | @ask _ β L f argument l r left right ihl ihr =>
    intro u q m γ ρ inj h
    cases q with
    | ret exit' payload' => cases exit' <;> cases h
    | ask g b left' right' =>
      have parts := LetCase.LocallyNameless.Tm.let₁.inj h
      obtain ⟨rfl, arguments⟩ := LetCase.LocallyNameless.Tm.op.inj parts.1
      have arms := LetCase.LocallyNameless.Tm.case.inj parts.2
      rw [payload_rename_inj argument b ρ inj arguments,
        ihl left' (armRenaming ρ _ _) (arm_injective ρ inj _ _) arms.2.1,
        ihr right' (armRenaming ρ _ _) (arm_injective ρ inj _ _) arms.2.2]

end Binary

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
