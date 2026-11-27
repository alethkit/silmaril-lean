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

/-! ## Pattern lets on pair slots commute

Two pattern lets on pair slots may be exchanged, and a pattern let on an
older pair slot may be moved in front of a bound tuple and the pattern lets
that unpack it. These are derived from native typed laws, like the
equation above. -/

section Interchange

variable [HasTy Φ (Ty α)]

/-- A pattern let on a pair of slots is natively equal to its body with the
two components renamed to those slots. -/
theorem let_pair_slots_proof {m : Nat} {Γ : BoundCtx (Ty α) m} {A B C : Ty α} (p q : Fin m)
    (hp : Γ.get p = A) (hq : Γ.get q = B) {body : LetCase.LocallyNameless.Tm Empty Φ (m + 2)}
    (hBody : HasType Φ Γ₀ ((Γ.snoc A).snoc B) body C) :
    Equiv false Γ₀ Γ (.let₂ (.pair (.bv p) (.bv q)) body)
      (body.rename (Fin.cases q (Fin.cases p (fun i => i)))) C := by
  subst hp
  subst hq
  have hA : HasType Φ Γ₀ Γ (.bv p) (Γ.get p) := .bv
  have hB : HasType Φ Γ₀ Γ (.bv q) (Γ.get q) := .bv
  have split := Equiv.pairBeta (pureEff := false) hA hB hBody
  have first := Equiv.letBeta (pureEff := false) Pure.bv hA (.let₁ hB.lift hBody)
  have first_eq : LetCase.LocallyNameless.Tm.instantiate
      (.let₁ (LetCase.LocallyNameless.Tm.lift (.bv q)) body) (.bv p) =
      .let₁ (.bv q) (LetCase.LocallyNameless.Tm.bsubst
        (LetCase.LocallyNameless.Tm.upSub (Fin.cases (.bv p) (fun i => .bv i))) body) := rfl
  rw [first_eq] at first
  obtain ⟨-, typed⟩ := first.hasType
  cases typed with
  | let₁ hV hZ =>
    cases hV
    have second := Equiv.letBeta (pureEff := false) Pure.bv hB hZ
    have second_eq : LetCase.LocallyNameless.Tm.instantiate
        (LetCase.LocallyNameless.Tm.bsubst
          (LetCase.LocallyNameless.Tm.upSub (Fin.cases (.bv p) (fun i => .bv i))) body)
        (.bv q) = body.rename (Fin.cases q (Fin.cases p (fun i => i))) := by
      simp only [LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst_comp]
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) body).trans
        (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename _ body)
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
    rw [second_eq] at second
    exact split.trans (first.trans second)

/-- Two pattern lets on pair slots commute. -/
theorem let_pair_pair_comm_proof {m : Nat} {Γ : BoundCtx (Ty α) m} {A B C D E : Ty α} (i j : Fin m)
    (hi : Γ.get i = .product C D) (hj : Γ.get j = .product A B)
    {body : LetCase.LocallyNameless.Tm Empty Φ (m + 4)}
    (hBody : HasType Φ Γ₀ ((((Γ.snoc C).snoc D).snoc A).snoc B) body E) :
    Equiv false Γ₀ Γ (.let₂ (.bv i) (.let₂ (.bv j.succ.succ) body))
      (.let₂ (.bv j) (.let₂ (.bv i.succ.succ) (body.rename afterPairPair))) E := by
  have hx : HasType Φ Γ₀ Γ (.bv j) (.product A B) := hj ▸ .bv
  have hy : HasType Φ Γ₀ Γ (.bv i) (.product C D) := hi ▸ .bv
  let ins := ((((BoundCtx.Renaming.succ Γ (.product A B)).up C).up D).up A).up B
  let K : LetCase.LocallyNameless.Tm Empty Φ (m + 1) :=
    .let₂ (.bv i.succ) (.let₂ (.bv 2) (body.rename ins.toFun))
  have hK : HasType Φ Γ₀ (Γ.snoc (.product A B)) K E :=
    .let₂ (HasType.rename (BoundCtx.Renaming.succ Γ (.product A B)) hy)
      (.let₂ (.bv (ι := (2 : Fin (m + 3)))) (HasType.rename ins hBody))
  have enter := Equiv.letBeta (pureEff := false) Pure.bv hx hK
  have inst_eq : LetCase.LocallyNameless.Tm.instantiate K (.bv j) =
      .let₂ (.bv i) (.let₂ (.bv j.succ.succ) body) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst,
      LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    congr 1
    refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) body).trans
      (LetCase.LocallyNameless.Tm.bsubst_id body)
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    exact Fin.cases rfl (fun i => rfl) i
  rw [inst_eq] at enter
  have eta := Equiv.let₁ (Equiv.pairEta (pureEff := false) hx).symm (.refl hK)
  have pull := Equiv.bindLetPair (pureEff := false) hx
    (.pair (.bv (ι := (1 : Fin (m + 2)))) (.bv (ι := (0 : Fin (m + 2))))) hK
  have hPair : HasType Φ Γ₀ ((Γ.snoc A).snoc B) (.pair (.bv 1) (.bv 0)) (.product A B) :=
    .pair (.bv (ι := (1 : Fin (m + 2)))) (.bv (ι := (0 : Fin (m + 2))))
  have beta := Equiv.letBeta (pureEff := false) (Pure.pair Pure.bv Pure.bv) hPair hK.underBinder.underBinder
  let past : BoundCtx.Renaming Γ ((Γ.snoc A).snoc B) :=
    (BoundCtx.Renaming.succ Γ A).comp (BoundCtx.Renaming.succ (Γ.snoc A) B)
  let ins2 := (((past.up C).up D).up A).up B
  have beta_eq : LetCase.LocallyNameless.Tm.instantiate K.underBinder.underBinder (.pair (.bv 1) (.bv 0)) =
      .let₂ (.bv i.succ.succ) (.let₂ (.pair (.bv 3) (.bv 2)) (body.rename ins2.toFun)) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.underBinder,
      LetCase.LocallyNameless.Tm.rename_comp, LetCase.LocallyNameless.Tm.rename,
      LetCase.LocallyNameless.Tm.bsubst, LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    congr 1
    refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) body).trans
      (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename ins2.toFun body)
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    exact Fin.cases rfl (fun i => rfl) i
  rw [beta_eq] at beta
  have hBody₂ : HasType Φ Γ₀ ((((((Γ.snoc A).snoc B).snoc C).snoc D).snoc A).snoc B)
      (body.rename ins2.toFun) E := HasType.rename ins2 hBody
  have slots := let_pair_slots_proof (Γ := (((Γ.snoc A).snoc B).snoc C).snoc D) 3 2 rfl rfl hBody₂
  have moved : (body.rename ins2.toFun).rename (Fin.cases 2 (Fin.cases 3 (fun i => i))) =
      body.rename afterPairPair := by
    rw [LetCase.LocallyNameless.Tm.rename_comp]
    apply LetCase.LocallyNameless.Tm.rename_congr
    intro l
    refine Fin.cases rfl (fun l => ?_) l
    refine Fin.cases rfl (fun l => ?_) l
    refine Fin.cases rfl (fun l => ?_) l
    exact Fin.cases rfl (fun l => rfl) l
  rw [moved] at slots
  have hy'' : HasType Φ Γ₀ ((Γ.snoc A).snoc B) (.bv i.succ.succ) (.product C D) := HasType.rename past hy
  exact enter.symm.trans (eta.trans (pull.trans (Equiv.let₂ (.refl hx)
    (beta.trans (Equiv.let₂ (.refl hy'') slots)))))

end Interchange

section Unpack

variable [HasTy Φ (Ty α)]

/-- A slot is typed at its type. -/
theorem slot_typed {k : Nat} {Γ : BoundCtx (Ty α) k} (i : Fin k) {A : Ty α} (h : Γ.get i = A) :
    HasType Φ Γ₀ Γ (.bv i) A := h ▸ .bv

/-- Unpacking is typed when the unpacked slot has the tuple type. -/
theorem unpackAt_typed_proof : (atoms : List α) → {k : Nat} → {Γ : BoundCtx (Ty α) k} → (i : Fin k) →
    Γ.get i = tupleTy atoms → {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (pairsTele atoms))} →
    {C : Ty α} → HasType Φ Γ₀ (extendCtx Γ (pairsTele atoms)) u C → HasType Φ Γ₀ Γ (unpackAt atoms i u) C
  | [], _, _, _, _, _, _, h => h
  | [_], _, _, _, _, _, _, h => h
  | _ :: d :: more, _, _, i, hi, _, _, h =>
    .let₂ (slot_typed i hi) (unpackAt_typed_proof (d :: more) 0 rfl h)

/-- Unpacking preserves native equations. -/
theorem unpackAt_congr_proof : (atoms : List α) → {k : Nat} → {Γ : BoundCtx (Ty α) k} → (i : Fin k) →
    Γ.get i = tupleTy atoms → {u v : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (pairsTele atoms))} →
    {C : Ty α} → Equiv false Γ₀ (extendCtx Γ (pairsTele atoms)) u v C →
    Equiv false Γ₀ Γ (unpackAt atoms i u) (unpackAt atoms i v) C
  | [], _, _, _, _, _, _, _, h => h
  | [_], _, _, _, _, _, _, _, h => h
  | _ :: d :: more, _, _, i, hi, _, _, _, h =>
    Equiv.let₂ (.refl (slot_typed i hi)) (unpackAt_congr_proof (d :: more) 0 rfl h)

/-- A pattern let on an older pair slot, under the unpacking of a tuple
slot, is natively equal to the pattern let in front of the unpacking. One
interchange of pattern lets is used for each pattern let of the
unpacking. -/
theorem unpack_pair_comm_proof : (atoms : List α) → {k : Nat} → {Γ : BoundCtx (Ty α) k} → (i j : Fin k) →
    Γ.get i = tupleTy atoms → {A B C : Ty α} → Γ.get j = .product A B →
    {body : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (pairsTele atoms) + 1 + 1)} →
    HasType Φ Γ₀ (((extendCtx Γ (pairsTele atoms)).snoc A).snoc B) body C →
    Equiv false Γ₀ Γ
      (unpackAt atoms i (.let₂ (.bv ((weakenTele Γ (pairsTele atoms)).toFun j)) body))
      (.let₂ (.bv j) (unpackAt atoms i.succ.succ
        (body.rename (pairPastTele Γ (pairsTele atoms) A B).toFun))) C
  | [], _, Γ, _, j, _, A, B, _, hj, body, hBody => by
    have same : body.rename (pairPastTele Γ (pairsTele ([] : List α)) A B).toFun = body :=
      (LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun _ => rfl) i) body).trans
        (LetCase.LocallyNameless.Tm.rename_id body)
    exact Equiv.let₂ (.refl (slot_typed j hj))
      (Eq.subst (motive := fun x => Equiv false Γ₀ (((extendCtx Γ (pairsTele ([] : List α))).snoc A).snoc B) body x _)
        same.symm (.refl hBody))
  | [c], _, Γ, _, j, _, A, B, _, hj, body, hBody => by
    have same : body.rename (pairPastTele Γ (pairsTele [c]) A B).toFun = body :=
      (LetCase.LocallyNameless.Tm.rename_congr (fun i => Fin.cases rfl (fun _ => rfl) i) body).trans
        (LetCase.LocallyNameless.Tm.rename_id body)
    exact Equiv.let₂ (.refl (slot_typed j hj))
      (Eq.subst (motive := fun x => Equiv false Γ₀ (((extendCtx Γ (pairsTele [c])).snoc A).snoc B) body x _)
        same.symm (.refl hBody))
  | c :: d :: more, _, Γ, i, j, hi, A, B, C, hj, body, hBody => by
    let R : Ty α := tupleTy (d :: more)
    let Γ₂ := (Γ.snoc (.base c)).snoc R
    have ih := unpack_pair_comm_proof (d :: more) (Γ := Γ₂) 0 j.succ.succ rfl hj hBody
    have hZ : HasType Φ Γ₀ ((Γ₂.snoc A).snoc B)
        (unpackAt (d :: more) (2 : Fin (_ + 4))
          (body.rename (pairPastTele Γ₂ (pairsTele (d :: more)) A B).toFun)) C :=
      unpackAt_typed_proof (d :: more) (Γ := (Γ₂.snoc A).snoc B) 2 rfl
        (HasType.rename (pairPastTele Γ₂ (pairsTele (d :: more)) A B) hBody)
    have comm := let_pair_pair_comm_proof i j hi hj hZ
    have moved : (unpackAt (d :: more) (2 : Fin (_ + 4))
        (body.rename (pairPastTele Γ₂ (pairsTele (d :: more)) A B).toFun)).rename afterPairPair =
        unpackAt (d :: more) (0 : Fin (_ + 4))
          (body.rename (pairPastTele Γ (pairsTele (c :: d :: more)) A B).toFun) := by
      have step := unpackAt_rename (Φ := Φ) (d :: more) (afterPairPairRenaming Γ (.base c) R A B) 2
        (body.rename (pairPastTele Γ₂ (pairsTele (d :: more)) A B).toFun)
      have total : pairPastTele Γ (pairsTele (c :: d :: more)) A B =
          (pairPastTele Γ₂ (pairsTele (d :: more)) A B).comp
            (upTele (afterPairPairRenaming Γ (.base c) R A B) (pairsTele (d :: more))) := by
        have outer := pairPastTele_cons (R :: pairsTele (d :: more)) Γ (.base c) A B
        rw [pairPastTele_cons (pairsTele (d :: more)) (Γ.snoc (.base c)) R A B] at outer
        rw [afterPairPair_split, ← upTele_comp]
        exact outer
      rw [total]
      exact step.trans (congrArg (unpackAt (d :: more) 0) (LetCase.LocallyNameless.Tm.rename_comp _ _ body))
    rw [moved] at comm
    exact (Equiv.let₂ (.refl (slot_typed i hi)) ih).trans comm

/-- A bound tuple that is unpacked, followed by a pattern let on an older
pair slot, is natively equal to the pattern let in front of the binding:

`let₁ E (unpack (let₂ x B)) = let₂ x (let₁ E↑↑ (unpack B′))`

where `unpack` is the sequence of pattern lets that unpacks the bound
tuple, `E↑↑` is `E` weakened past the two components, and `B′` is `B` with
the two components moved beneath the tuple slot and the slots of its
unpacking. `E` may be an effectful request. -/
theorem let_unpack_pair_comm_proof (atoms : List α) {k : Nat} {Δ : BoundCtx (Ty α) k} (j : Fin k)
    {A B C : Ty α} (hj : Δ.get j = .product A B) {E : LetCase.LocallyNameless.Tm Empty Φ k}
    (hE : HasType Φ Γ₀ Δ E (tupleTy atoms))
    {body : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (unpackTele atoms) + 1 + 1)}
    (hBody : HasType Φ Γ₀ (((extendCtx Δ (unpackTele atoms)).snoc A).snoc B) body C) :
    Equiv false Γ₀ Δ
      (.let₁ E (unpackAt atoms 0 (.let₂ (.bv ((weakenTele Δ (unpackTele atoms)).toFun j)) body)))
      (.let₂ (.bv j) (.let₁ (E.rename (pastPair Δ A B).toFun)
        (unpackAt atoms 0 (body.rename (pairPastTele Δ (unpackTele atoms) A B).toFun)))) C := by
  let X : Ty α := tupleTy atoms
  have inner := unpack_pair_comm_proof atoms (Γ := Δ.snoc X) 0 j.succ rfl hj hBody
  have hZ : HasType Φ Γ₀ (((Δ.snoc X).snoc A).snoc B)
      (unpackAt atoms (2 : Fin (k + 3)) (body.rename (pairPastTele (Δ.snoc X) (pairsTele atoms) A B).toFun)) C :=
    unpackAt_typed_proof atoms (Γ := ((Δ.snoc X).snoc A).snoc B) 2 rfl
      (HasType.rename (pairPastTele (Δ.snoc X) (pairsTele atoms) A B) hBody)
  have comm := let_pair_comm_proof j hj hE hZ
  have moved : (unpackAt atoms (2 : Fin (k + 3))
      (body.rename (pairPastTele (Δ.snoc X) (pairsTele atoms) A B).toFun)).rename afterPair =
      unpackAt atoms (0 : Fin (k + 3)) (body.rename (pairPastTele Δ (unpackTele atoms) A B).toFun) := by
    have step := unpackAt_rename (Φ := Φ) atoms (afterPairRenaming Δ X A B) 2
      (body.rename (pairPastTele (Δ.snoc X) (pairsTele atoms) A B).toFun)
    rw [pairPastTele_cons (pairsTele atoms) Δ X A B]
    exact step.trans (congrArg (unpackAt atoms 0) (LetCase.LocallyNameless.Tm.rename_comp _ _ body))
  rw [moved] at comm
  exact (Equiv.let₁ (.refl hE) inner).trans comm

end Unpack

/-! ## A tuple held across a chain of requests

The chain with its final destructuring removed, as a term in which the
slots of the chain, the first atom and the rest of the tuple are placed by
one renaming. -/

section Chain

variable [TaggedSignature α Φ]

mutual

/-- The chain with its final destructuring removed, as a term. One
renaming places the slots of the chain, the first atom and the rest of the
tuple. -/
def flatDelay : {a b : α} → {rest : List α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {t : LetCase.LocallyNameless.Tm Empty Φ m} →
    SpelledDelay a b rest Δ s L t → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    BoundCtx.Renaming ((Δ.snoc (.base a)).snoc (tupleTy (b :: rest))) Θ → LetCase.LocallyNameless.Tm Empty Φ k
  | _, _, _, _, _, _, _, .unpack (t := body) _, _, _, σ => body.rename σ.toFun
  | a, b, rest, _, Δ, _, _, .ask g argument reply, _, _, σ =>
    flatDelayed reply σ
      (.op g ((argTerm argument).rename ((pastPair Δ (.base a) (tupleTy (b :: rest))).comp σ).toFun))

/-- The same for the reply of a request, given the renamed request. The
first atom and the rest of the tuple are moved beneath the reply and the
slots of its unpacking. -/
def flatDelayed : {a b : α} → {rest : List α} → {tags : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {e t : LetCase.LocallyNameless.Tm Empty Φ m} →
    SpelledDelayed a b rest tags e Δ s L t → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    BoundCtx.Renaming ((Δ.snoc (.base a)).snoc (tupleTy (b :: rest))) Θ →
    LetCase.LocallyNameless.Tm Empty Φ k → LetCase.LocallyNameless.Tm Empty Φ k
  | a, b, rest, _, _, Δ, _, _, _, .bind atoms next, _, _, σ, e' =>
    .let₁ e' (unpackAt atoms 0 (flatDelay next
      ((pairPastTele Δ (unpackTele atoms) (.base a) (tupleTy (b :: rest))).comp (upTele σ (unpackTele atoms)))))

end

mutual

/-- The flattened chain commutes with renaming. -/
theorem flatDelay_rename : {a b : α} → {rest : List α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {t : LetCase.LocallyNameless.Tm Empty Φ m} →
    (d : SpelledDelay a b rest Δ s L t) → {k j : Nat} → {Θ : BoundCtx (Ty α) k} → {Θ' : BoundCtx (Ty α) j} →
    (σ : BoundCtx.Renaming ((Δ.snoc (.base a)).snoc (tupleTy (b :: rest))) Θ) → (π : BoundCtx.Renaming Θ Θ') →
    (flatDelay d σ).rename π.toFun = flatDelay d (σ.comp π)
  | _, _, _, _, _, _, _, .unpack _, _, _, _, _, σ, π => LetCase.LocallyNameless.Tm.rename_comp σ.toFun π.toFun _
  | a, b, rest, _, Δ, _, _, .ask g argument reply, _, _, _, _, σ, π => by
    have h := flatDelayed_rename reply σ π
      (.op g ((argTerm argument).rename ((pastPair Δ (.base a) (tupleTy (b :: rest))).comp σ).toFun))
    exact h.trans (congrArg (fun x => flatDelayed reply (σ.comp π) (.op g x))
      (LetCase.LocallyNameless.Tm.rename_comp _ _ (argTerm argument)))

/-- The same for the reply of a request. -/
theorem flatDelayed_rename : {a b : α} → {rest : List α} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {s : Slot Δ (tupleTy (a :: b :: rest))} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ m} → (d : SpelledDelayed a b rest tags e Δ s L t) → {k j : Nat} →
    {Θ : BoundCtx (Ty α) k} → {Θ' : BoundCtx (Ty α) j} →
    (σ : BoundCtx.Renaming ((Δ.snoc (.base a)).snoc (tupleTy (b :: rest))) Θ) → (π : BoundCtx.Renaming Θ Θ') →
    (e' : LetCase.LocallyNameless.Tm Empty Φ k) →
    (flatDelayed d σ e').rename π.toFun = flatDelayed d (σ.comp π) (e'.rename π.toFun)
  | a, b, rest, _, _, Δ, _, _, _, .bind atoms next, _, _, _, _, σ, π, e' => by
    let pp := pairPastTele Δ (unpackTele atoms) (.base a) (tupleTy (b :: rest))
    have h := flatDelay_rename next (pp.comp (upTele σ (unpackTele atoms))) (upTele π (unpackTele atoms))
    have lifted : (pp.comp (upTele σ (unpackTele atoms))).comp (upTele π (unpackTele atoms)) = pp.comp (upTele (σ.comp π) (unpackTele atoms)) :=
      congrArg (fun r => pp.comp r) (upTele_comp (unpackTele atoms) σ π)
    rw [lifted] at h
    have inner := unpackAt_rename (Φ := Φ) atoms (π.up (tupleTy atoms)) 0 (flatDelay next (pp.comp (upTele σ (unpackTele atoms))))
    exact congrArg (LetCase.LocallyNameless.Tm.let₁ (e'.rename π.toFun))
      (inner.trans (congrArg (unpackAt atoms 0) h))

end

mutual

/-- The flattened chain is typed where the first atom and the rest of the
tuple are slots. -/
theorem flatDelay_typed : {a b : α} → {rest : List α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {t : LetCase.LocallyNameless.Tm Empty Φ m} →
    (d : SpelledDelay a b rest Δ s L t) → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    (σ : BoundCtx.Renaming ((Δ.snoc (.base a)).snoc (tupleTy (b :: rest))) Θ) →
    HasType Φ Γ₀ Θ (flatDelay d σ) (packedExitType L)
  | _, _, _, _, _, _, _, .unpack later, _, _, σ => HasType.rename σ later.typing.toHasType
  | a, b, rest, _, Δ, _, _, .ask g argument reply, _, _, σ =>
    flatDelayed_typed reply σ _
      (HasType.rename ((pastPair Δ (.base a) (tupleTy (b :: rest))).comp σ)
        (Derivation.op (f := g) (argTyping argument)).toHasType)

/-- The same for the reply of a request. -/
theorem flatDelayed_typed : {a b : α} → {rest : List α} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {s : Slot Δ (tupleTy (a :: b :: rest))} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ m} → (d : SpelledDelayed a b rest tags e Δ s L t) → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (σ : BoundCtx.Renaming ((Δ.snoc (.base a)).snoc (tupleTy (b :: rest))) Θ) →
    (e' : LetCase.LocallyNameless.Tm Empty Φ k) → HasType Φ Γ₀ Θ e' (tagsTy tags) →
    HasType Φ Γ₀ Θ (flatDelayed d σ e') (packedExitType L)
  | a, b, rest, _, _, Δ, _, _, _, .bind atoms next, _, Θ, σ, _, he' =>
    .let₁ he' (unpackAt_typed_proof atoms (Γ := Θ.snoc (tupleTy atoms)) 0 rfl
      (flatDelay_typed next ((pairPastTele Δ (unpackTele atoms) (.base a) (tupleTy (b :: rest))).comp
        (upTele σ (unpackTele atoms)))))

end

mutual

/-- A chain with a held tuple, renamed, is natively equal to destructuring
the tuple first and then running the flattened chain. One commuting step is
used for each request of the chain and each pattern let that unpacks its
reply. -/
theorem delay_comm : {a b : α} → {rest : List α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {t : LetCase.LocallyNameless.Tm Empty Φ m} →
    (d : SpelledDelay a b rest Δ s L t) → {k : Nat} → {Δ' : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming Δ Δ') →
    Equiv false Γ₀ Δ' (t.rename ρ.toFun)
      (.let₂ (.bv (ρ.toFun s.1)) (flatDelay d ((ρ.up (.base a)).up (tupleTy (b :: rest)))))
      (packedExitType L)
  | _, _, _, _, _, _, _, .unpack later, _, _, ρ =>
    .refl (HasType.rename ρ (SpelledDelay.unpack later).typing.toHasType)
  | a, b, rest, _, Δ, _, _, .ask g argument reply, _, Δ', ρ => by
    have h := delayed_comm reply ρ (HasType.rename ρ (Derivation.op (f := g) (argTyping argument)).toHasType)
    have request : ((LetCase.LocallyNameless.Tm.op g (argTerm (Φ := Φ) argument)).rename ρ.toFun).rename
        (pastPair Δ' (.base a) (tupleTy (b :: rest))).toFun =
        .op g ((argTerm argument).rename ((pastPair Δ (.base a) (tupleTy (b :: rest))).comp
          ((ρ.up (.base a)).up (tupleTy (b :: rest)))).toFun) := by
      simp only [LetCase.LocallyNameless.Tm.rename, LetCase.LocallyNameless.Tm.rename_comp]
      rfl
    rw [request] at h
    exact h

/-- The same for the reply of a request, given the typing of the renamed
request. -/
theorem delayed_comm : {a b : α} → {rest : List α} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {s : Slot Δ (tupleTy (a :: b :: rest))} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ m} → (d : SpelledDelayed a b rest tags e Δ s L t) → {k : Nat} →
    {Δ' : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming Δ Δ') →
    HasType Φ Γ₀ Δ' (e.rename ρ.toFun) (tagsTy tags) →
    Equiv false Γ₀ Δ' (t.rename ρ.toFun)
      (.let₂ (.bv (ρ.toFun s.1))
        (flatDelayed d ((ρ.up (.base a)).up (tupleTy (b :: rest)))
          ((e.rename ρ.toFun).rename (pastPair Δ' (.base a) (tupleTy (b :: rest))).toFun)))
      (packedExitType L)
  | a, b, rest, _, _, Δ, s, e, _, @SpelledDelayed.bind _ _ _ _ _ _ _ _ _ _ atoms _ body next, _, Δ', ρ, he => by
    let T : Ty α := tupleTy (b :: rest)
    have ih := delay_comm next (upTele ρ (unpackTele atoms))
    have slotAt : (upTele ρ (unpackTele atoms)).toFun ((weakenTele Δ (unpackTele atoms)).toFun s.1) =
        (weakenTele Δ' (unpackTele atoms)).toFun (ρ.toFun s.1) :=
      congrArg (fun r => r.toFun s.1) (weakenTele_natural (unpackTele atoms) ρ)
    have ih' : Equiv false Γ₀ (extendCtx Δ' (unpackTele atoms)) (body.rename (upTele ρ (unpackTele atoms)).toFun)
        (.let₂ (.bv ((weakenTele Δ' (unpackTele atoms)).toFun (ρ.toFun s.1)))
          (flatDelay next (((upTele ρ (unpackTele atoms)).up (.base a)).up T))) (packedExitType L) := by
      rw [← slotAt]
      exact ih
    have typed := flatDelay_typed next (((upTele ρ (unpackTele atoms)).up (.base a)).up T)
    have slot : Δ'.get (ρ.toFun s.1) = .product (.base a) T := (ρ.typed s.1).trans s.2
    have comm := let_unpack_pair_comm_proof atoms (ρ.toFun s.1) slot he typed
    have moved : (flatDelay next (((upTele ρ (unpackTele atoms)).up (.base a)).up T)).rename
        (pairPastTele Δ' (unpackTele atoms) (.base a) T).toFun =
        flatDelay next ((pairPastTele Δ (unpackTele atoms) (.base a) T).comp (upTele ((ρ.up (.base a)).up T) (unpackTele atoms))) := by
      rw [flatDelay_rename, pairPastTele_natural]
    have comm' := Eq.subst (motive := fun x => Equiv false Γ₀ Δ'
      (.let₁ (e.rename ρ.toFun) (unpackAt atoms 0 (.let₂ (.bv ((weakenTele Δ' (unpackTele atoms)).toFun
        (ρ.toFun s.1))) (flatDelay next (((upTele ρ (unpackTele atoms)).up (.base a)).up T)))))
      (.let₂ (.bv (ρ.toFun s.1)) (.let₁ ((e.rename ρ.toFun).rename (pastPair Δ' (.base a) T).toFun)
        (unpackAt atoms 0 x))) (packedExitType L)) moved comm
    have renamed : (LetCase.LocallyNameless.Tm.let₁ e (unpackAt atoms 0 body)).rename ρ.toFun =
        .let₁ (e.rename ρ.toFun) (unpackAt atoms 0 (body.rename (upTele ρ (unpackTele atoms)).toFun)) :=
      congrArg (LetCase.LocallyNameless.Tm.let₁ (e.rename ρ.toFun))
        (unpackAt_rename (Φ := Φ) atoms (ρ.up (tupleTy atoms)) 0 body)
    rw [renamed]
    exact (Equiv.let₁ (.refl he) (unpackAt_congr_proof atoms (Γ := Δ'.snoc (tupleTy atoms)) 0 rfl ih')).trans comm'

end

end Chain

/-! ## Binding under a pending tuple

A binding in front of a pending tuple is moved under the full unpacking of
the tuple. The binding is given by its native account: its action on terms
and the equation that moves a pattern let on an older pair slot in front
of it. That equation is used once for each pattern let of the unpacking. -/

section Push

variable [TaggedSignature α Φ]

/-- The native account of a way to bind a telescope, taken after a
renaming of the base context. -/
theorem framed_after_proof {m k : Nat} {Ω : BoundCtx (Ty α) m} {Ω₁ : BoundCtx (Ty α) k} {tel : List (Ty α)}
    {wrap : CaseTree.Wrap Φ L Ω tel}
    {term : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
      LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel) → LetCase.LocallyNameless.Tm Empty Φ k}
    (framed : wrap.Framed term) (ρ : BoundCtx.Renaming Ω Ω₁) :
    CaseTree.Wrap.Framed (L := L) (Ω := Ω₁) (tel := tel) (fun ω => wrap (ρ.comp ω))
      (fun ω => term (ρ.comp ω)) where
  spec ω _ r := framed.spec (ρ.comp ω) r
  comm ω j _ _ hj _ hBody := framed.comm (ρ.comp ω) j hj hBody

theorem pushed_spec_proof {pending : Pending α} {n : Nat} {β : BoundCtx (Ty α) n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree pending β L t) :
    CaseTree.PushedSpec pending β tree := by
  induction tree with
  | ret exit payload => trivial
  | ask f argument reply ih => trivial
  | only atoms payload ih => trivial
  | split atoms next rest left right ihl ihr => trivial
  | unit body ih =>
    intro m Ω tel π wrap term framed
    have same : (CaseTree.pushed (CaseTree.unit body) π wrap).1 =
        term (BoundCtx.Renaming.succ Ω _) (_ : LetCase.LocallyNameless.Tm Empty Φ _) :=
      (framed.spec _ _).trans (congrArg _ (CaseTree.renamed_body_term body ((π.up _).comp (swapTele Ω tel _))))
    rw [← same]
    exact .refl (CaseTree.pushed (CaseTree.unit body) π wrap).2.typing.toHasType
  | atom a body ih =>
    intro m Ω tel π wrap term framed
    have same : (CaseTree.pushed (CaseTree.atom a body) π wrap).1 =
        term (BoundCtx.Renaming.succ Ω _) (_ : LetCase.LocallyNameless.Tm Empty Φ _) :=
      (framed.spec _ _).trans (congrArg _ (CaseTree.renamed_body_term body ((π.up _).comp (swapTele Ω tel _))))
    rw [← same]
    exact .refl (CaseTree.pushed (CaseTree.atom a body) π wrap).2.typing.toHasType
  | @pair _ Ξ L a b rest body later ih =>
    intro m Ω tel π wrap term framed
    let T : Ty α := tupleTy (a :: b :: rest)
    let T₂ : Ty α := tupleTy (b :: rest)
    let θ := (π.up T).comp (swapTele Ω tel T)
    let π₂ := ((π.up T).up (Ty.base a)).comp (pairPastTele Ω tel T (Ty.base a))
    have typed : HasType Φ Γ₀ (((extendCtx (Ω.snoc T) tel).snoc (Ty.base a)).snoc T₂)
        (body.rename ((θ.up (Ty.base a)).up T₂).toFun) (packedExitType L) :=
      HasType.rename ((θ.up _).up _) later.typing.toHasType
    have comm := framed.comm (BoundCtx.Renaming.succ Ω T) (0 : Fin (m + 1)) rfl typed
    have zero : (weakenTele (Ω.snoc T) tel).toFun 0 = θ.toFun 0 :=
      (congrArg (fun r => r.toFun 0) (swapTele_weaken tel Ω T)).symm
    rw [zero] at comm
    have next := ih π₂ (fun ω => wrap ((pastPair Ω T (Ty.base a)).comp ω))
      (fun ω => term ((pastPair Ω T (Ty.base a)).comp ω)) (framed_after_proof framed (pastPair Ω T (Ty.base a)))
    have inner : (((π.up T).comp (swapTele Ω tel T)).up (Ty.base a)).comp (swapTele (Ω.snoc T) tel (Ty.base a)) =
        ((π.up T).up (Ty.base a)).comp (pairPastTele Ω tel T (Ty.base a)) := by
      rw [← renaming_up_comp (π.up T) (swapTele Ω tel T) (Ty.base a)]
      rfl
    have e : ((θ.up (Ty.base a)).up T₂).comp (pairPastTele (Ω.snoc T) tel (Ty.base a) T₂) =
        (π₂.up T₂).comp (swapTele ((Ω.snoc T).snoc (Ty.base a)) tel T₂) := by
      show (((((π.up T).comp (swapTele Ω tel T)).up (Ty.base a)).up T₂).comp
        ((swapTele (Ω.snoc T) tel (Ty.base a)).up T₂)).comp
          (swapTele ((Ω.snoc T).snoc (Ty.base a)) tel T₂) = _
      rw [renaming_up_comp, inner]
    have moved : (body.rename ((θ.up (Ty.base a)).up T₂).toFun).rename
        (pairPastTele (Ω.snoc T) tel (Ty.base a) T₂).toFun =
        body.rename ((π₂.up T₂).comp (swapTele ((Ω.snoc T).snoc (Ty.base a)) tel T₂)).toFun :=
      (LetCase.LocallyNameless.Tm.rename_comp _ _ body).trans (congrArg (fun r => body.rename r.toFun) e)
    rw [moved] at comm
    exact comm.trans (Equiv.let₂ (.refl .bv) next)

/-- Binding a tuple by `E` and unpacking it has a native account. -/
theorem unpack_framed_proof (atoms : List α) {m : Nat} {Ω : BoundCtx (Ty α) m}
    (wrap : CaseTree.Wrap Φ L Ω (unpackTele atoms)) (E : LetCase.LocallyNameless.Tm Empty Φ m)
    (hE : HasType Φ Γ₀ Ω E (tupleTy atoms))
    (spec : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k} (ω : BoundCtx.Renaming Ω Ω')
      {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (unpackTele atoms))}
      (r : CaseTree .body (extendCtx Ω' (unpackTele atoms)) L u),
      (wrap ω r).1 = .let₁ (E.rename ω.toFun) (unpackAt atoms 0 u)) :
    wrap.Framed (fun ω u => .let₁ (E.rename ω.toFun) (unpackAt atoms 0 u)) where
  spec ω _ r := spec ω r
  comm ω j _ _ hj _ hBody := by
    have h := let_unpack_pair_comm_proof atoms j hj (HasType.rename ω hE) hBody
    rw [LetCase.LocallyNameless.Tm.rename_comp] at h
    exact h

end Push

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
      rw [ExitAt.term_rename, argTerm_rename]
    rw [term]
    exact .refl (CaseTree.ret exit (payload.rename ρ)).typing.toHasType
  | _, _, _, .ask f argument head, _, γ, ρ => by
    have request : (LetCase.LocallyNameless.Tm.op f (argTerm (Φ := Φ) argument)).rename ρ.toFun =
        .op f (argTerm (argument.rename ρ)) := by
      simp only [LetCase.LocallyNameless.Tm.rename, argTerm_rename]
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
  | _, _, _, _, .hold _ _ _ delay, _, _, ρ =>
    (delay_comm delay (ρ.up _)).trans (Equiv.let₂ (.refl .bv) (delay.normal_flat (ρ.up _)))

/-- The flattened chain, with the first atom and the rest of the tuple as
the two newest slots, is natively equal to the normal form of the chain. -/
theorem SpelledDelay.normal_flat : {a b : α} → {rest : List α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {t : LetCase.LocallyNameless.Tm Empty Φ m} →
    (d : SpelledDelay a b rest Δ s L t) → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    (σ : BoundCtx.Renaming Δ Θ) →
    Equiv false Γ₀ ((Θ.snoc (.base a)).snoc (tupleTy (b :: rest)))
      (flatDelay d ((σ.up (.base a)).up (tupleTy (b :: rest)))) (d.normal σ).1 (packedExitType L)
  | _, _, _, _, _, _, _, .unpack later, _, _, σ => later.normal_equiv (σ.up _)
  | a, b, rest, _, Δ, _, _, .ask g argument reply, _, Θ, σ => by
    let past : BoundCtx.Renaming Δ (Θ.snoc (.base a)) := σ.comp (BoundCtx.Renaming.succ Θ (.base a))
    have hE : HasType Φ Γ₀ (Θ.snoc (.base a)) (.op g (argTerm (argument.rename past))) (tagsTy (replyTags g)) :=
      (Derivation.op (f := g) (argTyping (argument.rename past))).toHasType
    have request : LetCase.LocallyNameless.Tm.op g ((argTerm (Φ := Φ) argument).rename
        ((pastPair Δ (.base a) (tupleTy (b :: rest))).comp
          ((σ.up (.base a)).up (tupleTy (b :: rest)))).toFun) =
        (LetCase.LocallyNameless.Tm.op g (argTerm (argument.rename past))).rename Fin.succ := by
      rw [← argTerm_rename argument past]
      simp only [LetCase.LocallyNameless.Tm.rename, LetCase.LocallyNameless.Tm.rename_comp]
      rfl
    have h := reply.normal_flat σ
      (fun {_ _} ω {_} r => ⟨_, .ask g (argument.rename (past.comp ω)) r⟩) _ hE
      (fun ω _ r => by
        show LetCase.LocallyNameless.Tm.let₁ (.op g (argTerm (argument.rename (past.comp ω)))) _ = _
        rw [← assembly_rename_comp, ← argTerm_rename]
        rfl)
    show Equiv false Γ₀ _ (flatDelayed reply _ (.op g ((argTerm argument).rename _))) _ _
    rw [request]
    exact h

/-- The same for the reply of a request. The request is given as a term
over the first atom, with the way the normal form asks it. -/
theorem SpelledDelayed.normal_flat : {a b : α} → {rest : List α} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {s : Slot Δ (tupleTy (a :: b :: rest))} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ m} → (d : SpelledDelayed a b rest tags e Δ s L t) → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (σ : BoundCtx.Renaming Δ Θ) →
    (asker : ∀ {j : Nat} {Ω : BoundCtx (Ty α) j}, BoundCtx.Renaming (Θ.snoc (.base a)) Ω →
      {u : LetCase.LocallyNameless.Tm Empty Φ (j + 1)} → CaseTree (.tags tags) (Ω.snoc (tagsTy tags)) L u →
      (v : LetCase.LocallyNameless.Tm Empty Φ j) × CaseTree .body Ω L v) →
    (E : LetCase.LocallyNameless.Tm Empty Φ (k + 1)) → HasType Φ Γ₀ (Θ.snoc (.base a)) E (tagsTy tags) →
    (∀ {j : Nat} {Ω : BoundCtx (Ty α) j} (ω : BoundCtx.Renaming (Θ.snoc (.base a)) Ω)
      {u : LetCase.LocallyNameless.Tm Empty Φ (j + 1)} (r : CaseTree (.tags tags) (Ω.snoc (tagsTy tags)) L u),
      (asker ω r).1 = .let₁ (E.rename ω.toFun) u) →
    Equiv false Γ₀ ((Θ.snoc (.base a)).snoc (tupleTy (b :: rest)))
      (flatDelayed d ((σ.up (.base a)).up (tupleTy (b :: rest))) (E.rename Fin.succ))
      (d.normal σ asker).1 (packedExitType L)
  | a, b, rest, _, _, Δ, _, _, _, .bind atoms next, _, Θ, σ, asker, E, hE, spec => by
    let T : Ty α := tupleTy (b :: rest)
    let pp := pairPastTele Θ (unpackTele atoms) (.base a) T
    have ih := (next.normal_flat (upTele σ (unpackTele atoms))).rename pp
    have moved : (flatDelay next (((upTele σ (unpackTele atoms)).up (.base a)).up T)).rename pp.toFun =
        flatDelay next ((pairPastTele Δ (unpackTele atoms) (.base a) T).comp (upTele ((σ.up (.base a)).up T) (unpackTele atoms))) := by
      rw [flatDelay_rename, pairPastTele_natural]
    rw [moved] at ih
    have push := pushed_spec_proof (next.normal (upTele σ (unpackTele atoms))).2 (swapTele Θ (unpackTele atoms) (.base a))
      (fun {_ _} ω {_} r => asker ω (.only atoms (CaseTree.packed atoms r)))
      (fun ω u => .let₁ (E.rename ω.toFun) (unpackAt atoms 0 u))
      (unpack_framed_proof atoms _ E hE (fun ω _ r => spec ω (.only atoms (CaseTree.packed atoms r))))
    exact (Equiv.let₁ (.refl (HasType.rename (BoundCtx.Renaming.succ _ T) hE))
      (unpackAt_congr_proof atoms (Γ := ((Θ.snoc (.base a)).snoc T).snoc (tupleTy atoms)) 0 rfl ih)).trans push

end

end Spelled

/-! ## Normal forms commute with renaming

The normal form of a spelled tree along a composite renaming is the
normal form along the first renaming, renamed along the second. For a
chain with a held tuple this uses the two commutations of renaming with
binding under a pending tuple. -/

section Natural

variable [TaggedSignature α Φ]

mutual

theorem Spelled.normal_renamed : {n : Nat} → {β : BoundCtx (Ty α) n} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → (d : Spelled β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → {k : Nat} → {δ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming β γ) →
    (π : BoundCtx.Renaming γ δ) →
    CaseTree.renamed (pending := .body) (d.normal ρ).2 π = d.normal (ρ.comp π)
  | _, _, _, .ret exit payload, _, _, _, _, ρ, π => by
    simp only [Spelled.normal, CaseTree.renamed]
    rw [assembly_rename_comp]
  | _, _, _, .ask f argument head, _, _, _, _, ρ, π => by
    have h := head.normal_renamed ρ π
    simp only [Spelled.normal, CaseTree.renamed]
    rw [assembly_rename_comp, h]

theorem SpelledHead.normal_renamed : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ n} → (d : SpelledHead tags e β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → {k : Nat} → {δ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming β γ) →
    (π : BoundCtx.Renaming γ δ) →
    CaseTree.renamed (pending := .tags tags) (β := γ.snoc (tagsTy tags)) (d.normal ρ).2 π =
      d.normal (ρ.comp π)
  | _, _, _, _, _, .bind reply, _, _, _, _, ρ, π => reply.normal_renamed ρ π
  | _, _, _, _, _, .destruct a b rest later, _, γ, _, δ, ρ, π => by
    have h := later.normal_renamed (armRenaming ρ (tupleTy (a :: b :: rest)) (.base a)) ((π.up _).up _)
    have e : (armRenaming ρ (tupleTy (a :: b :: rest)) (.base a)).comp ((π.up _).up _) =
        armRenaming (ρ.comp π) (tupleTy (a :: b :: rest)) (.base a) :=
      renaming_ext (Fin.cases rfl (fun _ => rfl))
    rw [e] at h
    simp only [SpelledHead.normal, CaseTree.renamed]
    rw [h]
  | _, _, _, _, _, .branch atoms next rest left right, _, γ, _, δ, ρ, π => by
    have hl := left.normal_renamed (ρ.comp (BoundCtx.Renaming.succ γ (tagsTy (atoms :: next :: rest)))) (π.up _)
    have hr := right.normal_renamed (ρ.comp (BoundCtx.Renaming.succ γ (tagsTy (atoms :: next :: rest)))) (π.up _)
    have e : (ρ.comp (BoundCtx.Renaming.succ γ (tagsTy (atoms :: next :: rest)))).comp (π.up _) =
        (ρ.comp π).comp (BoundCtx.Renaming.succ δ (tagsTy (atoms :: next :: rest))) :=
      renaming_ext (fun _ => rfl)
    rw [e] at hl hr
    simp only [SpelledHead.normal, CaseTree.renamed]
    rw [hl, hr]

theorem SpelledTags.normal_renamed : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → (d : SpelledTags tags β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → {k : Nat} → {δ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming β γ) →
    (π : BoundCtx.Renaming γ δ) →
    CaseTree.renamed (pending := .tags tags) (β := γ.snoc (tagsTy tags)) (d.normal ρ).2 π =
      d.normal (ρ.comp π)
  | _, _, _, _, .only atoms payload, _, _, _, _, ρ, π => by
    have h := payload.normal_renamed ρ π
    simp only [SpelledTags.normal, CaseTree.renamed]
    rw [h]
  | _, _, _, _, .split atoms next rest left right, _, _, _, _, ρ, π => by
    have hl := left.normal_renamed (ρ.up _) (π.up _)
    have hr := right.normal_renamed (ρ.up _) (π.up _)
    rw [renaming_up_comp] at hl hr
    simp only [SpelledTags.normal, CaseTree.renamed]
    rw [hl, hr]

theorem SpelledTuple.normal_renamed : {n : Nat} → {β : BoundCtx (Ty α) n} → {atoms : List α} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → (d : SpelledTuple atoms β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → {k : Nat} → {δ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming β γ) →
    (π : BoundCtx.Renaming γ δ) →
    CaseTree.renamed (pending := .tuple atoms) (β := γ.snoc (tupleTy atoms)) (d.normal ρ).2 π =
      d.normal (ρ.comp π)
  | _, _, _, _, .unit body, _, _, _, _, ρ, π => by
    have h := body.normal_renamed (ρ.up _) (π.up _)
    rw [renaming_up_comp] at h
    simp only [SpelledTuple.normal, CaseTree.renamed]
    rw [h]
  | _, _, _, _, .atom a body, _, _, _, _, ρ, π => by
    have h := body.normal_renamed (ρ.up _) (π.up _)
    rw [renaming_up_comp] at h
    simp only [SpelledTuple.normal, CaseTree.renamed]
    rw [h]
  | _, _, _, _, .pair a b rest later, _, _, _, _, ρ, π => by
    have h := later.normal_renamed ((ρ.up _).up _) ((π.up _).up _)
    rw [renaming_up_comp, renaming_up_comp] at h
    simp only [SpelledTuple.normal, CaseTree.renamed]
    rw [h]
  | _, _, _, _, .hold a b rest delay, _, _, _, _, ρ, π => by
    have h := delay.normal_renamed (ρ.up (tupleTy (a :: b :: rest))) (π.up (tupleTy (a :: b :: rest)))
    rw [renaming_up_comp] at h
    simp only [SpelledTuple.normal, CaseTree.renamed]
    rw [h]

/-- The normal form of a chain with a held tuple commutes with renaming. -/
theorem SpelledDelay.normal_renamed : {a b : α} → {rest : List α} → {n : Nat} → {Δ : BoundCtx (Ty α) n} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    (d : SpelledDelay a b rest Δ s L t) → {m : Nat} → {Θ : BoundCtx (Ty α) m} → {k : Nat} →
    {δ : BoundCtx (Ty α) k} → (σ : BoundCtx.Renaming Δ Θ) → (π : BoundCtx.Renaming Θ δ) →
    CaseTree.renamed (pending := .tuple (b :: rest)) (β := (Θ.snoc (.base a)).snoc (tupleTy (b :: rest)))
      (d.normal σ).2 (π.up (.base a)) = d.normal (σ.comp π)
  | a, _, _, _, _, _, _, .unpack later, _, _, _, _, σ, π => by
    have h := later.normal_renamed (σ.up (.base a)) (π.up (.base a))
    rw [renaming_up_comp] at h
    exact h
  | a, b, rest, _, Δ, _, _, .ask g argument reply, _, Θ, _, δ, σ, π => by
    have h := reply.normal_renamed σ π
      (fun {_ _} ω {_} r =>
        ⟨_, .ask g (argument.rename ((σ.comp (BoundCtx.Renaming.succ Θ (.base a))).comp ω)) r⟩)
      (fun ω₁ _ r _ _ ω₂ => by
        simp only [CaseTree.renamed]
        rw [assembly_rename_comp]
        rfl)
    exact h

/-- The same for the reply of a request, when the way the normal form asks
the request commutes with renaming. -/
theorem SpelledDelayed.normal_renamed : {a b : α} → {rest : List α} → {tags : List (List α)} → {n : Nat} →
    {Δ : BoundCtx (Ty α) n} → {s : Slot Δ (tupleTy (a :: b :: rest))} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ n} → (d : SpelledDelayed a b rest tags e Δ s L t) → {m : Nat} →
    {Θ : BoundCtx (Ty α) m} → {k : Nat} → {δ : BoundCtx (Ty α) k} →
    (σ : BoundCtx.Renaming Δ Θ) → (π : BoundCtx.Renaming Θ δ) →
    (asker : ∀ {j : Nat} {Ω : BoundCtx (Ty α) j}, BoundCtx.Renaming (Θ.snoc (.base a)) Ω →
      {u : LetCase.LocallyNameless.Tm Empty Φ (j + 1)} → CaseTree (.tags tags) (Ω.snoc (tagsTy tags)) L u →
      (v : LetCase.LocallyNameless.Tm Empty Φ j) × CaseTree .body Ω L v) →
    (∀ {j : Nat} {Ω : BoundCtx (Ty α) j} (ω : BoundCtx.Renaming (Θ.snoc (.base a)) Ω)
      {u : LetCase.LocallyNameless.Tm Empty Φ (j + 1)} (r : CaseTree (.tags tags) (Ω.snoc (tagsTy tags)) L u)
      {i : Nat} {Ω' : BoundCtx (Ty α) i} (ω' : BoundCtx.Renaming Ω Ω'),
      CaseTree.renamed (pending := .body) (asker ω r).2 ω' =
        asker (ω.comp ω') (CaseTree.renamed (pending := .tags tags) (β := Ω.snoc (tagsTy tags)) r ω').2) →
    CaseTree.renamed (pending := .tuple (b :: rest)) (β := (Θ.snoc (.base a)).snoc (tupleTy (b :: rest)))
      (d.normal σ asker).2 (π.up (.base a)) = d.normal (σ.comp π) (fun ω => asker ((π.up (.base a)).comp ω))
  | a, b, rest, _, _, _, _, _, _, .bind atoms next, _, Θ, _, δ, σ, π, asker, natural => by
    have ih := next.normal_renamed (upTele σ (unpackTele atoms)) (upTele π (unpackTele atoms))
    rw [upTele_comp] at ih
    have post := CaseTree.renamed_pushed (next.normal (upTele σ (unpackTele atoms))).2 (swapTele Θ (unpackTele atoms) (.base a))
      (fun {_ _} ω {_} r => asker ω (.only atoms (CaseTree.packed atoms r)))
      (fun ω₁ _ r _ _ ω₂ => by
        have h := natural ω₁ (.only atoms (CaseTree.packed atoms r)) ω₂
        simp only [CaseTree.renamed] at h
        rw [CaseTree.packed_renamed] at h
        exact h)
      (π.up (.base a))
    have pre := CaseTree.pushed_renamed (next.normal (upTele σ (unpackTele atoms))).2 ((upTele π (unpackTele atoms)).up (.base a))
      (swapTele δ (unpackTele atoms) (.base a))
      (fun {_ _} ω {_} r => asker ((π.up (.base a)).comp ω) (.only atoms (CaseTree.packed atoms r)))
    rw [swapTele_natural] at post
    rw [ih] at pre
    exact post.trans pre.symm

end

end Natural

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
