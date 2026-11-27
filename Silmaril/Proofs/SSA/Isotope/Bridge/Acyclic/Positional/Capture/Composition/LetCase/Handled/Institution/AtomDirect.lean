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

/-! ## A case commutes with a pattern let on a pair slot

A case on a slot whose two arms destructure the same older pair slot is
natively equal to destructuring first. The case is not moved across any
request and keeps its scrutinee. -/

section CasePair

variable [HasTy Φ (Ty α)]

/-- A term over a pair slot is natively equal to destructuring the slot
and using the pair of components in its place:

`K[x] = let₂ x (K[(a, b)])`

for a slot `x` of pair type. `K` may be any typed term, with requests and
cases. This is the common step of the equations that move a pattern let
on a pair slot: pure-let beta at the slot, pair eta, the sequencing law
that pulls a pattern let out of the scrutinee of a let, and pure-let beta
at the pair of components. -/
theorem slot_pair_split_proof {m : Nat} {Δ : BoundCtx (Ty α) m} {A B C : Ty α} (j : Fin m)
    (hj : Δ.get j = .product A B) {K : LetCase.LocallyNameless.Tm Empty Φ (m + 1)}
    (hK : HasType Φ Γ₀ (Δ.snoc (.product A B)) K C) :
    Equiv false Γ₀ Δ (LetCase.LocallyNameless.Tm.instantiate K (.bv j))
      (.let₂ (.bv j) (LetCase.LocallyNameless.Tm.instantiate K.underBinder.underBinder
        (.pair (.bv 1) (.bv 0)))) C := by
  have hx : HasType Φ Γ₀ Δ (.bv j) (.product A B) := hj ▸ .bv
  have enter := Equiv.letBeta (pureEff := false) Pure.bv hx hK
  have eta := Equiv.let₁ (Equiv.pairEta (pureEff := false) hx).symm (.refl hK)
  have pull := Equiv.bindLetPair (pureEff := false) hx
    (.pair (.bv (ι := (1 : Fin (m + 2)))) (.bv (ι := (0 : Fin (m + 2))))) hK
  have hPair : HasType Φ Γ₀ ((Δ.snoc A).snoc B) (.pair (.bv 1) (.bv 0)) (.product A B) :=
    .pair (.bv (ι := (1 : Fin (m + 2)))) (.bv (ι := (0 : Fin (m + 2))))
  have beta := Equiv.letBeta (pureEff := false) (Pure.pair Pure.bv Pure.bv) hPair hK.underBinder.underBinder
  exact enter.symm.trans (eta.trans (pull.trans (Equiv.let₂ (.refl hx) beta)))

/-- A case on a slot whose two arms destructure the same older pair slot
is natively equal to destructuring the pair slot first:

`case s (let₂ x L) (let₂ x R) = let₂ x (case s L′ R′)`

where `s` is a slot of sum type, `x` a slot of pair type, and `L′`, `R′`
are the arms with the two components moved beneath the arm's payload. The
case stays on the same scrutinee and keeps its place; only the pure
destructuring moves. -/
theorem case_pair_comm_proof {m : Nat} {Δ : BoundCtx (Ty α) m} {A B X Y C : Ty α} (i j : Fin m)
    (hi : Δ.get i = .coprod X Y) (hj : Δ.get j = .product A B)
    {l r : LetCase.LocallyNameless.Tm Empty Φ (m + 3)}
    (hl : HasType Φ Γ₀ (((Δ.snoc X).snoc A).snoc B) l C)
    (hr : HasType Φ Γ₀ (((Δ.snoc Y).snoc A).snoc B) r C) :
    Equiv false Γ₀ Δ (.case (.bv i) (.let₂ (.bv j.succ) l) (.let₂ (.bv j.succ) r))
      (.let₂ (.bv j) (.case (.bv i.succ.succ) (l.rename afterPair) (r.rename afterPair))) C := by
  have hs : HasType Φ Γ₀ Δ (.bv i) (.coprod X Y) := hi ▸ .bv
  let insX := (((BoundCtx.Renaming.succ Δ (.product A B)).up X).up A).up B
  let insY := (((BoundCtx.Renaming.succ Δ (.product A B)).up Y).up A).up B
  let K : LetCase.LocallyNameless.Tm Empty Φ (m + 1) :=
    .case (.bv i.succ) (.let₂ (.bv 1) (l.rename insX.toFun)) (.let₂ (.bv 1) (r.rename insY.toFun))
  have hK : HasType Φ Γ₀ (Δ.snoc (.product A B)) K C :=
    .case (HasType.rename (BoundCtx.Renaming.succ Δ (.product A B)) hs)
      (.let₂ (.bv (ι := (1 : Fin (m + 2)))) (HasType.rename insX hl))
      (.let₂ (.bv (ι := (1 : Fin (m + 2)))) (HasType.rename insY hr))
  have split := slot_pair_split_proof j hj hK
  have inst_eq : LetCase.LocallyNameless.Tm.instantiate K (.bv j) =
      .case (.bv i) (.let₂ (.bv j.succ) l) (.let₂ (.bv j.succ) r) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.bsubst,
      LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    · congr 1
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) l).trans
        (LetCase.LocallyNameless.Tm.bsubst_id l)
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
    · congr 1
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) r).trans
        (LetCase.LocallyNameless.Tm.bsubst_id r)
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
  rw [inst_eq] at split
  let past : BoundCtx.Renaming Δ ((Δ.snoc A).snoc B) :=
    (BoundCtx.Renaming.succ Δ A).comp (BoundCtx.Renaming.succ (Δ.snoc A) B)
  let insX2 := ((past.up X).up A).up B
  let insY2 := ((past.up Y).up A).up B
  have beta_eq : LetCase.LocallyNameless.Tm.instantiate K.underBinder.underBinder (.pair (.bv 1) (.bv 0)) =
      .case (.bv i.succ.succ) (.let₂ (.pair (.bv 2) (.bv 1)) (l.rename insX2.toFun))
        (.let₂ (.pair (.bv 2) (.bv 1)) (r.rename insY2.toFun)) := by
    simp only [K, LetCase.LocallyNameless.Tm.instantiate, LetCase.LocallyNameless.Tm.underBinder,
      LetCase.LocallyNameless.Tm.rename_comp, LetCase.LocallyNameless.Tm.rename,
      LetCase.LocallyNameless.Tm.bsubst, LetCase.LocallyNameless.Tm.bsubst_rename]
    congr 1
    · congr 1
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) l).trans
        (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename insX2.toFun l)
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
    · congr 1
      refine (LetCase.LocallyNameless.Tm.bsubst_congr (fun i => ?_) r).trans
        (LetCase.LocallyNameless.Tm.bsubst_bv_eq_rename insY2.toFun r)
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => rfl) i
  rw [beta_eq] at split
  have slotsX := let_pair_slots_proof (Γ := ((Δ.snoc A).snoc B).snoc X) 2 1 rfl rfl (HasType.rename insX2 hl)
  have slotsY := let_pair_slots_proof (Γ := ((Δ.snoc A).snoc B).snoc Y) 2 1 rfl rfl (HasType.rename insY2 hr)
  have movedX : (l.rename insX2.toFun).rename (Fin.cases 1 (Fin.cases 2 (fun i => i))) =
      l.rename afterPair := by
    rw [LetCase.LocallyNameless.Tm.rename_comp]
    apply LetCase.LocallyNameless.Tm.rename_congr
    intro i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    exact Fin.cases rfl (fun i => rfl) i
  have movedY : (r.rename insY2.toFun).rename (Fin.cases 1 (Fin.cases 2 (fun i => i))) =
      r.rename afterPair := by
    rw [LetCase.LocallyNameless.Tm.rename_comp]
    apply LetCase.LocallyNameless.Tm.rename_congr
    intro i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    exact Fin.cases rfl (fun i => rfl) i
  rw [movedX] at slotsX
  rw [movedY] at slotsY
  have hs'' : HasType Φ Γ₀ ((Δ.snoc A).snoc B) (.bv i.succ.succ) (.coprod X Y) := HasType.rename past hs
  have hx : HasType Φ Γ₀ Δ (.bv j) (.product A B) := hj ▸ .bv
  exact split.trans (Equiv.let₂ (.refl hx) (Equiv.case (.refl hs'') slotsX slotsY))

end CasePair

/-! ## Moving a whole unpacking

The unpacking of an older tuple slot moves in front of a binding, and in
front of a case whose arms both unpack it, by induction on the tuple. -/

section Out

variable [HasTy Φ (Ty α)]

/-- The whole unpacking of an older tuple slot moves in front of an action
on terms that moves single pattern lets. -/
theorem unpack_out_proof {C : Ty α} {m : Nat} {Ω : BoundCtx (Ty α) m} {tel : List (Ty α)}
    {term : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
      LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel) → LetCase.LocallyNameless.Tm Empty Φ k}
    (frame : PairFrame C Ω tel term) :
    (H : List α) → {k : Nat} → {Ω' : BoundCtx (Ty α) k} → (ω : BoundCtx.Renaming Ω Ω') → (j : Fin k) →
    Ω'.get j = tupleTy H →
    {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize (teleSize k tel) (pairsTele H))} →
    HasType Φ Γ₀ (extendCtx (extendCtx Ω' tel) (pairsTele H)) u C →
    Equiv false Γ₀ Ω' (term ω (unpackAt H ((weakenTele Ω' tel).toFun j) u))
      (unpackAt H j (term (ω.comp (weakenTele Ω' (pairsTele H)))
        (u.rename (swapTeles Ω' tel (pairsTele H)).toFun))) C
  | [], _, Ω', ω, _, _, u, hu =>
    Eq.subst (motive := fun x => Equiv false Γ₀ Ω' (term ω u)
      (term (ω.comp (weakenTele Ω' (pairsTele ([] : List α)))) x) C)
      (LetCase.LocallyNameless.Tm.rename_id u).symm (.refl (frame.typed ω hu))
  | [c], _, Ω', ω, _, _, u, hu =>
    Eq.subst (motive := fun x => Equiv false Γ₀ Ω' (term ω u)
      (term (ω.comp (weakenTele Ω' (pairsTele [c]))) x) C)
      (LetCase.LocallyNameless.Tm.rename_id u).symm (.refl (frame.typed ω hu))
  | c :: d :: more, k, Ω', ω, j, hj, u, hu => by
    let R : Ty α := tupleTy (d :: more)
    let pp := pairPastTele Ω' tel (.base c) R
    have hB : HasType Φ Γ₀ (((extendCtx Ω' tel).snoc (.base c)).snoc R) (unpackAt (d :: more) 0 u) C :=
      unpackAt_typed_proof (d :: more) (Γ := ((extendCtx Ω' tel).snoc (.base c)).snoc R) 0 rfl hu
    have comm := frame.comm ω j hj hB
    have e1 : (unpackAt (d :: more) (0 : Fin (teleSize k tel + 1 + 1)) u).rename pp.toFun =
        unpackAt (d :: more) ((weakenTele ((Ω'.snoc (.base c)).snoc R) tel).toFun 0)
          (u.rename (upTele pp (pairsTele (d :: more))).toFun) :=
      (unpackAt_rename (Φ := Φ) (d :: more) pp 0 u).trans
        (congrArg (fun i => unpackAt (d :: more) i (u.rename (upTele pp (pairsTele (d :: more))).toFun))
          (pairPastTele_zero tel Ω' (.base c) R))
    have comm' := Eq.subst (motive := fun x => Equiv false Γ₀ Ω'
      (term ω (.let₂ (.bv ((weakenTele Ω' tel).toFun j)) (unpackAt (d :: more) 0 u)))
      (.let₂ (.bv j) (term (ω.comp (pastPair Ω' (.base c) R)) x)) C) e1 comm
    have ih := unpack_out_proof frame (d :: more) (ω.comp (pastPair Ω' (.base c) R)) (0 : Fin (k + 2)) rfl
      (HasType.rename (upTele pp (pairsTele (d :: more))) hu)
    have e2 : (u.rename (upTele pp (pairsTele (d :: more))).toFun).rename
        (swapTeles ((Ω'.snoc (.base c)).snoc R) tel (pairsTele (d :: more))).toFun =
        u.rename (swapTeles Ω' tel (pairsTele (c :: d :: more))).toFun :=
      (LetCase.LocallyNameless.Tm.rename_comp _ _ u).trans
        (congrArg (fun r : BoundCtx.Renaming _ _ => u.rename r.toFun)
          (swapTeles_pair (pairsTele (d :: more)) Ω' tel (.base c) R).symm)
    have ih' := Eq.subst (motive := fun x => Equiv false Γ₀ ((Ω'.snoc (.base c)).snoc R)
      (term (ω.comp (pastPair Ω' (.base c) R)) (unpackAt (d :: more)
        ((weakenTele ((Ω'.snoc (.base c)).snoc R) tel).toFun 0)
        (u.rename (upTele pp (pairsTele (d :: more))).toFun)))
      (unpackAt (d :: more) 0 (term ((ω.comp (pastPair Ω' (.base c) R)).comp
        (weakenTele ((Ω'.snoc (.base c)).snoc R) (pairsTele (d :: more)))) x)) C) e2 ih
    exact comm'.trans (Equiv.let₂ (.refl (slot_typed j hj)) ih')

/-- The whole unpacking of an older tuple slot, done in both arms of a
case on a slot, moves in front of the case. The case stays on the same
scrutinee. One exchange of the case with a pattern let is used for each
pattern let of the unpacking. -/
theorem case_unpack_out_proof {C : Ty α} : (H : List α) → {k : Nat} → {Γ : BoundCtx (Ty α) k} →
    (i j : Fin k) → {X Y : Ty α} → Γ.get i = .coprod X Y → Γ.get j = tupleTy H →
    {l r : LetCase.LocallyNameless.Tm Empty Φ (teleSize (k + 1) (pairsTele H))} →
    HasType Φ Γ₀ (extendCtx (Γ.snoc X) (pairsTele H)) l C →
    HasType Φ Γ₀ (extendCtx (Γ.snoc Y) (pairsTele H)) r C →
    Equiv false Γ₀ Γ (.case (.bv i) (unpackAt H j.succ l) (unpackAt H j.succ r))
      (unpackAt H j (.case (.bv ((weakenTele Γ (pairsTele H)).toFun i))
        (l.rename (swapTeles Γ [X] (pairsTele H)).toFun)
        (r.rename (swapTeles Γ [Y] (pairsTele H)).toFun))) C
  | [], _, Γ, i, _, X, Y, hi, _, l, r, hl, hr =>
    Equiv.case (.refl (slot_typed i hi))
      (Eq.subst (motive := fun x => Equiv false Γ₀ (Γ.snoc X) l x C)
        (LetCase.LocallyNameless.Tm.rename_id l).symm (.refl hl))
      (Eq.subst (motive := fun x => Equiv false Γ₀ (Γ.snoc Y) r x C)
        (LetCase.LocallyNameless.Tm.rename_id r).symm (.refl hr))
  | [_], _, Γ, i, _, X, Y, hi, _, l, r, hl, hr =>
    Equiv.case (.refl (slot_typed i hi))
      (Eq.subst (motive := fun x => Equiv false Γ₀ (Γ.snoc X) l x C)
        (LetCase.LocallyNameless.Tm.rename_id l).symm (.refl hl))
      (Eq.subst (motive := fun x => Equiv false Γ₀ (Γ.snoc Y) r x C)
        (LetCase.LocallyNameless.Tm.rename_id r).symm (.refl hr))
  | c :: d :: more, k, Γ, i, j, X, Y, hi, hj, l, r, hl, hr => by
    let R : Ty α := tupleTy (d :: more)
    let Γ₂ := (Γ.snoc (.base c)).snoc R
    have hl₁ : HasType Φ Γ₀ (((Γ.snoc X).snoc (.base c)).snoc R) (unpackAt (d :: more) 0 l) C :=
      unpackAt_typed_proof (d :: more) (Γ := ((Γ.snoc X).snoc (.base c)).snoc R) 0 rfl hl
    have hr₁ : HasType Φ Γ₀ (((Γ.snoc Y).snoc (.base c)).snoc R) (unpackAt (d :: more) 0 r) C :=
      unpackAt_typed_proof (d :: more) (Γ := ((Γ.snoc Y).snoc (.base c)).snoc R) 0 rfl hr
    have comm := case_pair_comm_proof i j hi hj hl₁ hr₁
    have movedL := unpackAt_rename (Φ := Φ) (d :: more) (afterPairRenaming Γ X (.base c) R) 0 l
    have movedR := unpackAt_rename (Φ := Φ) (d :: more) (afterPairRenaming Γ Y (.base c) R) 0 r
    have ih := case_unpack_out_proof (C := C) (d :: more) (Γ := Γ₂) i.succ.succ 0 hi rfl
      (HasType.rename (upTele (afterPairRenaming Γ X (.base c) R) (pairsTele (d :: more))) hl)
      (HasType.rename (upTele (afterPairRenaming Γ Y (.base c) R) (pairsTele (d :: more))) hr)
    have total (Z : Ty α) (t : LetCase.LocallyNameless.Tm Empty Φ (teleSize (k + 1) (pairsTele (c :: d :: more)))) :
        (t.rename (upTele (afterPairRenaming Γ Z (.base c) R) (pairsTele (d :: more))).toFun).rename
          (swapTeles Γ₂ [Z] (pairsTele (d :: more))).toFun =
        t.rename (swapTeles Γ [Z] (pairsTele (c :: d :: more))).toFun := by
      have e := swapTeles_pair (pairsTele (d :: more)) Γ [Z] (.base c) R
      rw [pairPastTele_single] at e
      exact (LetCase.LocallyNameless.Tm.rename_comp _ _ t).trans
        (congrArg (fun r : BoundCtx.Renaming _ _ => t.rename r.toFun) e.symm)
    have comm' := Eq.subst (motive := fun x => Equiv false Γ₀ Γ
      (.case (.bv i) (.let₂ (.bv j.succ) (unpackAt (d :: more) 0 l)) (.let₂ (.bv j.succ) (unpackAt (d :: more) 0 r)))
      (.let₂ (.bv j) x) C)
      (congrArg₂ (fun x y => LetCase.LocallyNameless.Tm.case (.bv i.succ.succ) x y) movedL movedR) comm
    have ih' := Eq.subst (motive := fun x => Equiv false Γ₀ Γ₂
      (.case (.bv i.succ.succ)
        (unpackAt (d :: more) (1 : Fin (k + 3))
          (l.rename (upTele (afterPairRenaming Γ X (.base c) R) (pairsTele (d :: more))).toFun))
        (unpackAt (d :: more) (1 : Fin (k + 3))
          (r.rename (upTele (afterPairRenaming Γ Y (.base c) R) (pairsTele (d :: more))).toFun)))
      (unpackAt (d :: more) 0 x) C)
      (congrArg₂ (fun x y => LetCase.LocallyNameless.Tm.case
        (.bv ((weakenTele Γ₂ (pairsTele (d :: more))).toFun i.succ.succ)) x y) (total X l) (total Y r)) ih
    exact comm'.trans (Equiv.let₂ (.refl (slot_typed j hj)) ih')

end Out

/-- A native equation between terms equal to the given ones. -/
theorem equiv_cast [HasTy Φ (Ty α)] {k : Nat} {Γ : BoundCtx (Ty α) k} {C : Ty α}
    {x y x' y' : LetCase.LocallyNameless.Tm Empty Φ k} (h : Equiv false Γ₀ Γ x y C) (ex : x = x') (ey : y = y') :
    Equiv false Γ₀ Γ x' y' C := by
  subst ex
  subst ey
  exact h

/-! ## A tuple held across a chain of requests

The chain with the destructurings of the held tuple removed from its
branches, as a term in which the slots of the chain, the first atom and
the rest of the tuple are placed by one renaming. -/

section Chain

variable [TaggedSignature α Φ]

omit [TaggedSignature α Φ] in
/-- Moving two slots beneath a slot commutes with renaming. -/
theorem afterPair_natural {m k : Nat} {Δ : BoundCtx (Ty α) m} {Δ' : BoundCtx (Ty α) k}
    (ρ : BoundCtx.Renaming Δ Δ') (X A B : Ty α) :
    (((ρ.up X).up A).up B).comp (afterPairRenaming Δ' X A B) =
      (afterPairRenaming Δ X A B).comp (((ρ.up A).up B).up X) :=
  renaming_ext (Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun _ => rfl) i) i))

mutual

/-- The chain with the destructurings of the held tuple removed, as a
term. One renaming places the slots of the chain, the first atom and the
rest of the tuple. -/
def flatDelay : {a b : α} → {rest : List α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {t : LetCase.LocallyNameless.Tm Empty Φ m} →
    SpelledDelay a b rest Δ s L t → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    BoundCtx.Renaming ((Δ.snoc (.base a)).snoc (tupleTy (b :: rest))) Θ → LetCase.LocallyNameless.Tm Empty Φ k
  | _, _, _, _, _, _, _, .unpack (t := body) _, _, _, σ => body.rename σ.toFun
  | a, b, rest, _, Δ, _, _, .ask g argument reply, _, _, σ =>
    .let₁ (.op g ((argTerm argument).rename ((pastPair Δ (.base a) (tupleTy (b :: rest))).comp σ).toFun))
      (flatTags reply ((afterPairRenaming Δ (tagsTy (replyTags g)) (.base a) (tupleTy (b :: rest))).comp
        (σ.up (tagsTy (replyTags g)))))

/-- The same for the bound reply of a request. The renaming also places
the reply slot. -/
def flatTags : {a b : α} → {rest : List α} → {tags : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} →
    SpelledDelayTags a b rest tags Δ s L t → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    BoundCtx.Renaming (((Δ.snoc (tagsTy tags)).snoc (.base a)).snoc (tupleTy (b :: rest))) Θ →
    LetCase.LocallyNameless.Tm Empty Φ k
  | a, b, rest, _, _, Δ, _, _, .only atoms next, _, _, σ =>
    unpackAt atoms (σ.toFun 2) (flatDelay next
      ((pairPastTele (Δ.snoc (tupleTy atoms)) (pairsTele atoms) (.base a) (tupleTy (b :: rest))).comp
        (upTele σ (pairsTele atoms))))
  | a, b, rest, _, _, Δ, _, _, .split atoms nxt more left right, _, _, σ =>
    .case (.bv (σ.toFun 2))
      (unpackAt atoms 0 (flatDelay left
        ((pairPastTele (Δ.snoc (tagsTy (atoms :: nxt :: more))) (unpackTele atoms) (.base a)
          (tupleTy (b :: rest))).comp (upTele σ (unpackTele atoms)))))
      (flatTags right
        ((afterPairRenaming (Δ.snoc (tagsTy (atoms :: nxt :: more))) (tagsTy (nxt :: more)) (.base a)
          (tupleTy (b :: rest))).comp (σ.up (tagsTy (nxt :: more)))))

  | _, _, _, _, _, _, _, _, .keep _ _ _ kept, _, _, σ => flatKept kept σ

/-- The same for a subchain with a fresh tuple kept packed. The unpacking
of the fresh tuple stays in place. -/
def flatKept : {a b : α} → {rest fresh : List α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {x : Slot Δ (tupleTy fresh)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ m} → SpelledKept a b rest fresh Δ s x L t → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    BoundCtx.Renaming ((Δ.snoc (.base a)).snoc (tupleTy (b :: rest))) Θ → LetCase.LocallyNameless.Tm Empty Φ k
  | a, b, rest, fresh, _, Δ, _, x, _, .release next, _, _, σ =>
    unpackAt fresh (σ.toFun x.1.succ.succ) (flatDelay next
      ((pairPastTele Δ (pairsTele fresh) (.base a) (tupleTy (b :: rest))).comp (upTele σ (pairsTele fresh))))
  | a, b, rest, _, _, Δ, _, _, _, .ask g argument reply, _, _, σ =>
    .let₁ (.op g ((argTerm argument).rename ((pastPair Δ (.base a) (tupleTy (b :: rest))).comp σ).toFun))
      (flatKeptTags reply ((afterPairRenaming Δ (tagsTy (replyTags g)) (.base a) (tupleTy (b :: rest))).comp
        (σ.up (tagsTy (replyTags g)))))

/-- The same for the bound reply of a request of such a subchain. -/
def flatKeptTags : {a b : α} → {rest fresh : List α} → {tags : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {x : Slot Δ (tupleTy fresh)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → SpelledKeptTags a b rest fresh tags Δ s x L t → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → BoundCtx.Renaming (((Δ.snoc (tagsTy tags)).snoc (.base a)).snoc (tupleTy (b :: rest))) Θ → LetCase.LocallyNameless.Tm Empty Φ k
  | a, b, rest, _, _, _, Δ, _, _, _, .only atoms next, _, _, σ =>
    unpackAt atoms (σ.toFun 2) (flatKept next
      ((pairPastTele (Δ.snoc (tupleTy atoms)) (pairsTele atoms) (.base a) (tupleTy (b :: rest))).comp
        (upTele σ (pairsTele atoms))))

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
    let Rt : Ty α := tagsTy (replyTags g)
    have h := flatTags_rename reply
      ((afterPairRenaming Δ Rt (.base a) (tupleTy (b :: rest))).comp (σ.up Rt)) (π.up Rt)
    have e : ((afterPairRenaming Δ Rt (.base a) (tupleTy (b :: rest))).comp (σ.up Rt)).comp (π.up Rt) =
        (afterPairRenaming Δ Rt (.base a) (tupleTy (b :: rest))).comp ((σ.comp π).up Rt) :=
      congrArg (fun r => (afterPairRenaming Δ Rt (.base a) (tupleTy (b :: rest))).comp r)
        (renaming_up_comp σ π Rt)
    exact congrArg₂ LetCase.LocallyNameless.Tm.let₁
      (congrArg (LetCase.LocallyNameless.Tm.op g)
        (LetCase.LocallyNameless.Tm.rename_comp _ _ (argTerm argument)))
      (h.trans (congrArg (flatTags reply) e))

/-- The same for the bound reply of a request. -/
theorem flatTags_rename : {a b : α} → {rest : List α} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {s : Slot Δ (tupleTy (a :: b :: rest))} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → (d : SpelledDelayTags a b rest tags Δ s L t) →
    {k j : Nat} → {Θ : BoundCtx (Ty α) k} → {Θ' : BoundCtx (Ty α) j} →
    (σ : BoundCtx.Renaming (((Δ.snoc (tagsTy tags)).snoc (.base a)).snoc (tupleTy (b :: rest))) Θ) →
    (π : BoundCtx.Renaming Θ Θ') → (flatTags d σ).rename π.toFun = flatTags d (σ.comp π)
  | a, b, rest, _, _, Δ, _, _, .only atoms next, _, _, _, _, σ, π => by
    let pp := pairPastTele (Δ.snoc (tupleTy atoms)) (pairsTele atoms) (.base a) (tupleTy (b :: rest))
    have h := flatDelay_rename next (pp.comp (upTele σ (pairsTele atoms))) (upTele π (pairsTele atoms))
    have e : (pp.comp (upTele σ (pairsTele atoms))).comp (upTele π (pairsTele atoms)) =
        pp.comp (upTele (σ.comp π) (pairsTele atoms)) :=
      congrArg (fun r => pp.comp r) (upTele_comp (pairsTele atoms) σ π)
    exact (unpackAt_rename (Φ := Φ) atoms π (σ.toFun 2) _).trans
      (congrArg (unpackAt atoms (π.toFun (σ.toFun 2))) (h.trans (congrArg (flatDelay next) e)))
  | a, b, rest, _, _, Δ, _, _, .split atoms nxt more left right, _, _, _, _, σ, π => by
    let Rt : Ty α := tagsTy (atoms :: nxt :: more)
    let Y : Ty α := tagsTy (nxt :: more)
    let pp := pairPastTele (Δ.snoc Rt) (unpackTele atoms) (.base a) (tupleTy (b :: rest))
    have hl := flatDelay_rename left (pp.comp (upTele σ (unpackTele atoms))) (upTele π (unpackTele atoms))
    have el : (pp.comp (upTele σ (unpackTele atoms))).comp (upTele π (unpackTele atoms)) =
        pp.comp (upTele (σ.comp π) (unpackTele atoms)) :=
      congrArg (fun r => pp.comp r) (upTele_comp (unpackTele atoms) σ π)
    have hr := flatTags_rename right
      ((afterPairRenaming (Δ.snoc Rt) Y (.base a) (tupleTy (b :: rest))).comp (σ.up Y)) (π.up Y)
    have er : ((afterPairRenaming (Δ.snoc Rt) Y (.base a) (tupleTy (b :: rest))).comp (σ.up Y)).comp (π.up Y) =
        (afterPairRenaming (Δ.snoc Rt) Y (.base a) (tupleTy (b :: rest))).comp ((σ.comp π).up Y) :=
      congrArg (fun r => (afterPairRenaming (Δ.snoc Rt) Y (.base a) (tupleTy (b :: rest))).comp r)
        (renaming_up_comp σ π Y)
    exact congrArg₂ (LetCase.LocallyNameless.Tm.case (.bv (π.toFun (σ.toFun 2))))
      ((unpackAt_rename (Φ := Φ) atoms (π.up (tupleTy atoms)) 0 _).trans
        (congrArg (unpackAt atoms 0) (hl.trans (congrArg (flatDelay left) el))))
      (hr.trans (congrArg (flatTags right) er))

  | _, _, _, _, _, _, _, _, .keep _ _ _ kept, _, _, _, _, σ, π => flatKept_rename kept σ π

/-- The same for a subchain with a fresh tuple kept packed. -/
theorem flatKept_rename : {a b : α} → {rest fresh : List α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {x : Slot Δ (tupleTy fresh)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ m} → (d : SpelledKept a b rest fresh Δ s x L t) → {k j : Nat} →
    {Θ : BoundCtx (Ty α) k} → {Θ' : BoundCtx (Ty α) j} →
    (σ : BoundCtx.Renaming ((Δ.snoc (.base a)).snoc (tupleTy (b :: rest))) Θ) → (π : BoundCtx.Renaming Θ Θ') →
    (flatKept d σ).rename π.toFun = flatKept d (σ.comp π)
  | a, b, rest, fresh, _, Δ, _, x, _, .release next, _, _, _, _, σ, π => by
    let pp := pairPastTele Δ (pairsTele fresh) (.base a) (tupleTy (b :: rest))
    have h := flatDelay_rename next (pp.comp (upTele σ (pairsTele fresh))) (upTele π (pairsTele fresh))
    have e : (pp.comp (upTele σ (pairsTele fresh))).comp (upTele π (pairsTele fresh)) =
        pp.comp (upTele (σ.comp π) (pairsTele fresh)) :=
      congrArg (fun r => pp.comp r) (upTele_comp (pairsTele fresh) σ π)
    exact (unpackAt_rename (Φ := Φ) fresh π (σ.toFun x.1.succ.succ) _).trans
      (congrArg (unpackAt fresh (π.toFun (σ.toFun x.1.succ.succ))) (h.trans (congrArg (flatDelay next) e)))
  | a, b, rest, _, _, Δ, _, _, _, .ask g argument reply, _, _, _, _, σ, π => by
    let Rt : Ty α := tagsTy (replyTags g)
    have h := flatKeptTags_rename reply
      ((afterPairRenaming Δ Rt (.base a) (tupleTy (b :: rest))).comp (σ.up Rt)) (π.up Rt)
    have e : ((afterPairRenaming Δ Rt (.base a) (tupleTy (b :: rest))).comp (σ.up Rt)).comp (π.up Rt) =
        (afterPairRenaming Δ Rt (.base a) (tupleTy (b :: rest))).comp ((σ.comp π).up Rt) :=
      congrArg (fun r => (afterPairRenaming Δ Rt (.base a) (tupleTy (b :: rest))).comp r)
        (renaming_up_comp σ π Rt)
    exact congrArg₂ LetCase.LocallyNameless.Tm.let₁
      (congrArg (LetCase.LocallyNameless.Tm.op g)
        (LetCase.LocallyNameless.Tm.rename_comp _ _ (argTerm argument)))
      (h.trans (congrArg (flatKeptTags reply) e))

/-- The same for the bound reply of a request of such a subchain. -/
theorem flatKeptTags_rename : {a b : α} → {rest fresh : List α} → {tags : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {x : Slot Δ (tupleTy fresh)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → (d : SpelledKeptTags a b rest fresh tags Δ s x L t) → {k j : Nat} →
    {Θ : BoundCtx (Ty α) k} → {Θ' : BoundCtx (Ty α) j} →
    (σ : BoundCtx.Renaming (((Δ.snoc (tagsTy tags)).snoc (.base a)).snoc (tupleTy (b :: rest))) Θ) → (π : BoundCtx.Renaming Θ Θ') →
    (flatKeptTags d σ).rename π.toFun = flatKeptTags d (σ.comp π)
  | a, b, rest, _, _, _, Δ, _, _, _, .only atoms next, _, _, _, _, σ, π => by
    let pp := pairPastTele (Δ.snoc (tupleTy atoms)) (pairsTele atoms) (.base a) (tupleTy (b :: rest))
    have h := flatKept_rename next (pp.comp (upTele σ (pairsTele atoms))) (upTele π (pairsTele atoms))
    have e : (pp.comp (upTele σ (pairsTele atoms))).comp (upTele π (pairsTele atoms)) =
        pp.comp (upTele (σ.comp π) (pairsTele atoms)) :=
      congrArg (fun r => pp.comp r) (upTele_comp (pairsTele atoms) σ π)
    exact (unpackAt_rename (Φ := Φ) atoms π (σ.toFun 2) _).trans
      (congrArg (unpackAt atoms (π.toFun (σ.toFun 2))) (h.trans (congrArg (flatKept next) e)))

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
    .let₁ (HasType.rename ((pastPair Δ (.base a) (tupleTy (b :: rest))).comp σ)
        (Derivation.op (f := g) (argTyping argument)).toHasType)
      (flatTags_typed reply _)

/-- The same for the bound reply of a request. -/
theorem flatTags_typed : {a b : α} → {rest : List α} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {s : Slot Δ (tupleTy (a :: b :: rest))} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → (d : SpelledDelayTags a b rest tags Δ s L t) →
    {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    (σ : BoundCtx.Renaming (((Δ.snoc (tagsTy tags)).snoc (.base a)).snoc (tupleTy (b :: rest))) Θ) →
    HasType Φ Γ₀ Θ (flatTags d σ) (packedExitType L)
  | _, _, _, _, _, _, _, _, .only atoms next, _, _, σ =>
    unpackAt_typed_proof atoms (σ.toFun 2) (σ.typed 2) (flatDelay_typed next _)
  | _, _, _, _, _, _, _, _, .split atoms _ _ left right, _, Θ, σ =>
    .case (slot_typed (σ.toFun 2) (σ.typed 2))
      (unpackAt_typed_proof atoms (Γ := Θ.snoc (tupleTy atoms)) 0 rfl (flatDelay_typed left _))
      (flatTags_typed right _)

  | _, _, _, _, _, _, _, _, .keep _ _ _ kept, _, _, σ => flatKept_typed kept σ

/-- The same for a subchain with a fresh tuple kept packed. -/
theorem flatKept_typed : {a b : α} → {rest fresh : List α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {x : Slot Δ (tupleTy fresh)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ m} → (d : SpelledKept a b rest fresh Δ s x L t) → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (σ : BoundCtx.Renaming ((Δ.snoc (.base a)).snoc (tupleTy (b :: rest))) Θ) →
    HasType Φ Γ₀ Θ (flatKept d σ) (packedExitType L)
  | _, _, _, fresh, _, _, _, x, _, .release next, _, _, σ =>
    unpackAt_typed_proof fresh (σ.toFun x.1.succ.succ) ((σ.typed x.1.succ.succ).trans x.2)
      (flatDelay_typed next _)
  | a, b, rest, _, _, Δ, _, _, _, .ask g argument reply, _, _, σ =>
    .let₁ (HasType.rename ((pastPair Δ (.base a) (tupleTy (b :: rest))).comp σ)
        (Derivation.op (f := g) (argTyping argument)).toHasType)
      (flatKeptTags_typed reply _)

/-- The same for the bound reply of a request of such a subchain. -/
theorem flatKeptTags_typed : {a b : α} → {rest fresh : List α} → {tags : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {x : Slot Δ (tupleTy fresh)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → (d : SpelledKeptTags a b rest fresh tags Δ s x L t) → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (σ : BoundCtx.Renaming (((Δ.snoc (tagsTy tags)).snoc (.base a)).snoc (tupleTy (b :: rest))) Θ) →
    HasType Φ Γ₀ Θ (flatKeptTags d σ) (packedExitType L)
  | _, _, _, _, _, _, _, _, _, _, .only atoms next, _, _, σ =>
    unpackAt_typed_proof atoms (σ.toFun 2) (σ.typed 2) (flatKept_typed next _)

end

mutual

/-- A chain with a held tuple, renamed, is natively equal to destructuring
the tuple first and then running the flattened chain. The destructuring is
moved out of every branch: past each request, past each pattern let that
unpacks a reply, and out of both arms of each case. No case is moved. -/
theorem delay_comm : {a b : α} → {rest : List α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {t : LetCase.LocallyNameless.Tm Empty Φ m} →
    (d : SpelledDelay a b rest Δ s L t) → {k : Nat} → {Δ' : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming Δ Δ') →
    Equiv false Γ₀ Δ' (t.rename ρ.toFun)
      (.let₂ (.bv (ρ.toFun s.1)) (flatDelay d ((ρ.up (.base a)).up (tupleTy (b :: rest)))))
      (packedExitType L)
  | _, _, _, _, _, _, _, .unpack later, _, _, ρ =>
    .refl (HasType.rename ρ (SpelledDelay.unpack later).typing.toHasType)
  | a, b, rest, _, Δ, s, _, .ask g argument reply, _, Δ', ρ => by
    let Rt : Ty α := tagsTy (replyTags g)
    let T : Ty α := tupleTy (b :: rest)
    have ih := tags_comm reply ρ
    have he : HasType Φ Γ₀ Δ' ((LetCase.LocallyNameless.Tm.op g (argTerm (Φ := Φ) argument)).rename ρ.toFun) Rt :=
      HasType.rename ρ (Derivation.op (f := g) (argTyping argument)).toHasType
    have typed := flatTags_typed reply (((ρ.up Rt).up (.base a)).up T)
    have slot : Δ'.get (ρ.toFun s.1) = .product (.base a) T := (ρ.typed s.1).trans s.2
    have comm := let_pair_comm_proof (ρ.toFun s.1) slot he typed
    have request : ((LetCase.LocallyNameless.Tm.op g (argTerm (Φ := Φ) argument)).rename ρ.toFun).rename
        (fun i => i.succ.succ) =
        .op g ((argTerm argument).rename ((pastPair Δ (.base a) T).comp ((ρ.up (.base a)).up T)).toFun) := by
      simp only [LetCase.LocallyNameless.Tm.rename, LetCase.LocallyNameless.Tm.rename_comp]
      rfl
    have body : (flatTags reply (((ρ.up Rt).up (.base a)).up T)).rename afterPair =
        flatTags reply ((afterPairRenaming Δ Rt (.base a) T).comp (((ρ.up (.base a)).up T).up Rt)) :=
      (flatTags_rename reply _ (afterPairRenaming Δ' Rt (.base a) T)).trans
        (congrArg (flatTags reply) (afterPair_natural ρ Rt (.base a) T))
    have comm' := Eq.subst (motive := fun x => Equiv false Γ₀ Δ'
      (.let₁ ((LetCase.LocallyNameless.Tm.op g (argTerm (Φ := Φ) argument)).rename ρ.toFun)
        (.let₂ (.bv (ρ.toFun s.1).succ) (flatTags reply (((ρ.up Rt).up (.base a)).up T))))
      (.let₂ (.bv (ρ.toFun s.1)) x) (packedExitType L))
      (congrArg₂ LetCase.LocallyNameless.Tm.let₁ request body) comm
    exact (Equiv.let₁ (.refl he) ih).trans comm'

/-- The same for the bound reply of a request, under its slot. -/
theorem tags_comm : {a b : α} → {rest : List α} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {s : Slot Δ (tupleTy (a :: b :: rest))} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → (d : SpelledDelayTags a b rest tags Δ s L t) →
    {k : Nat} → {Δ' : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming Δ Δ') →
    Equiv false Γ₀ (Δ'.snoc (tagsTy tags)) (t.rename (ρ.up (tagsTy tags)).toFun)
      (.let₂ (.bv (ρ.toFun s.1).succ)
        (flatTags d (((ρ.up (tagsTy tags)).up (.base a)).up (tupleTy (b :: rest)))))
      (packedExitType L)
  | a, b, rest, _, _, Δ, s, _, @SpelledDelayTags.only _ _ _ _ _ _ _ _ _ _ atoms body next, _, Δ', ρ => by
    let X : Ty α := tupleTy atoms
    let T : Ty α := tupleTy (b :: rest)
    have ih := delay_comm next (upTele ρ (unpackTele atoms))
    have slotAt : (upTele ρ (unpackTele atoms)).toFun ((weakenTele Δ (unpackTele atoms)).toFun s.1) =
        (weakenTele (Δ'.snoc X) (pairsTele atoms)).toFun (ρ.toFun s.1).succ :=
      congrArg (fun r => r.toFun s.1) (weakenTele_natural (unpackTele atoms) ρ)
    have ih' : Equiv false Γ₀ (extendCtx (Δ'.snoc X) (pairsTele atoms))
        (body.rename (upTele ρ (unpackTele atoms)).toFun)
        (.let₂ (.bv ((weakenTele (Δ'.snoc X) (pairsTele atoms)).toFun (ρ.toFun s.1).succ))
          (flatDelay next (((upTele ρ (unpackTele atoms)).up (.base a)).up T))) (packedExitType L) := by
      rw [← slotAt]
      exact ih
    have typed := flatDelay_typed next (((upTele ρ (unpackTele atoms)).up (.base a)).up T)
    have slot : (Δ'.snoc X).get (ρ.toFun s.1).succ = .product (.base a) T := (ρ.typed s.1).trans s.2
    have comm := unpack_pair_comm_proof atoms (Γ := Δ'.snoc X) 0 (ρ.toFun s.1).succ rfl slot typed
    have moved : (flatDelay next (((upTele ρ (unpackTele atoms)).up (.base a)).up T)).rename
        (pairPastTele (Δ'.snoc X) (pairsTele atoms) (.base a) T).toFun =
        flatDelay next ((pairPastTele (Δ.snoc X) (pairsTele atoms) (.base a) T).comp
          (upTele (((ρ.up X).up (.base a)).up T) (pairsTele atoms))) :=
      (flatDelay_rename next _ (pairPastTele (Δ'.snoc X) (pairsTele atoms) (.base a) T)).trans
        (congrArg (flatDelay next) (pairPastTele_natural (pairsTele atoms) (ρ.up X) (.base a) T).symm)
    have comm' := Eq.subst (motive := fun x => Equiv false Γ₀ (Δ'.snoc X)
      (unpackAt atoms 0 (.let₂ (.bv ((weakenTele (Δ'.snoc X) (pairsTele atoms)).toFun (ρ.toFun s.1).succ))
        (flatDelay next (((upTele ρ (unpackTele atoms)).up (.base a)).up T))))
      (.let₂ (.bv (ρ.toFun s.1).succ) (unpackAt atoms 2 x)) (packedExitType L)) moved comm
    have renamed : (unpackAt atoms 0 body).rename (ρ.up X).toFun =
        unpackAt atoms 0 (body.rename (upTele ρ (unpackTele atoms)).toFun) :=
      unpackAt_rename (Φ := Φ) atoms (ρ.up X) 0 body
    exact Eq.subst (motive := fun x => Equiv false Γ₀ (Δ'.snoc X) x
      (.let₂ (.bv (ρ.toFun s.1).succ)
        (flatTags (SpelledDelayTags.only atoms next) (((ρ.up X).up (.base a)).up T))) (packedExitType L))
      renamed.symm ((unpackAt_congr_proof atoms (Γ := Δ'.snoc X) 0 rfl ih').trans comm')
  | a, b, rest, _, _, Δ, s, _, @SpelledDelayTags.split _ _ _ _ _ _ _ _ _ _ atoms nxt more l r left right,
      k, Δ', ρ => by
    let Rt : Ty α := tagsTy (atoms :: nxt :: more)
    let X : Ty α := tupleTy atoms
    let Y : Ty α := tagsTy (nxt :: more)
    let T : Ty α := tupleTy (b :: rest)
    let j : Fin (k + 1) := (ρ.toFun s.1).succ
    -- the first arm
    have ihl := delay_comm left (upTele ρ (Rt :: unpackTele atoms))
    have slotAt : (upTele ρ (Rt :: unpackTele atoms)).toFun ((weakenTele Δ (Rt :: unpackTele atoms)).toFun s.1) =
        (weakenTele ((Δ'.snoc Rt).snoc X) (pairsTele atoms)).toFun j.succ :=
      congrArg (fun r => r.toFun s.1) (weakenTele_natural (Rt :: unpackTele atoms) ρ)
    have ihl' : Equiv false Γ₀ (extendCtx ((Δ'.snoc Rt).snoc X) (pairsTele atoms))
        (l.rename (upTele ρ (Rt :: unpackTele atoms)).toFun)
        (.let₂ (.bv ((weakenTele ((Δ'.snoc Rt).snoc X) (pairsTele atoms)).toFun j.succ))
          (flatDelay left (((upTele ρ (Rt :: unpackTele atoms)).up (.base a)).up T))) (packedExitType L) := by
      rw [← slotAt]
      exact ihl
    have typedl := flatDelay_typed left (((upTele ρ (Rt :: unpackTele atoms)).up (.base a)).up T)
    have slotl : ((Δ'.snoc Rt).snoc X).get j.succ = .product (.base a) T := (ρ.typed s.1).trans s.2
    have comml := unpack_pair_comm_proof atoms (Γ := (Δ'.snoc Rt).snoc X) 0 j.succ rfl slotl typedl
    have arml := (unpackAt_congr_proof atoms (Γ := (Δ'.snoc Rt).snoc X) 0 rfl ihl').trans comml
    -- the other arms
    have ihr := tags_comm right (ρ.up Rt)
    -- the case
    have slot : (Δ'.snoc Rt).get j = .product (.base a) T := (ρ.typed s.1).trans s.2
    have hl₁ : HasType Φ Γ₀ ((((Δ'.snoc Rt).snoc X).snoc (.base a)).snoc T)
        (unpackAt atoms (2 : Fin (k + 4))
          ((flatDelay left (((upTele ρ (Rt :: unpackTele atoms)).up (.base a)).up T)).rename
            (pairPastTele ((Δ'.snoc Rt).snoc X) (pairsTele atoms) (.base a) T).toFun)) (packedExitType L) :=
      unpackAt_typed_proof atoms (Γ := (((Δ'.snoc Rt).snoc X).snoc (.base a)).snoc T) 2 rfl
        (HasType.rename (pairPastTele ((Δ'.snoc Rt).snoc X) (pairsTele atoms) (.base a) T) typedl)
    have hr₁ := flatTags_typed right ((((ρ.up Rt).up Y).up (.base a)).up T)
    have comm := case_pair_comm_proof (Δ := Δ'.snoc Rt) (X := X) (Y := Y) 0 j rfl slot hl₁ hr₁
    have movedl : (unpackAt atoms (2 : Fin (k + 4))
        ((flatDelay left (((upTele ρ (Rt :: unpackTele atoms)).up (.base a)).up T)).rename
          (pairPastTele ((Δ'.snoc Rt).snoc X) (pairsTele atoms) (.base a) T).toFun)).rename afterPair =
        unpackAt atoms (0 : Fin (k + 4)) (flatDelay left
          ((pairPastTele (Δ.snoc Rt) (unpackTele atoms) (.base a) T).comp
            (upTele (((ρ.up Rt).up (.base a)).up T) (unpackTele atoms)))) := by
      have step := unpackAt_rename (Φ := Φ) atoms (afterPairRenaming (Δ'.snoc Rt) X (.base a) T) 2
        ((flatDelay left (((upTele ρ (Rt :: unpackTele atoms)).up (.base a)).up T)).rename
          (pairPastTele ((Δ'.snoc Rt).snoc X) (pairsTele atoms) (.base a) T).toFun)
      have inner : ((flatDelay left (((upTele ρ (Rt :: unpackTele atoms)).up (.base a)).up T)).rename
          (pairPastTele ((Δ'.snoc Rt).snoc X) (pairsTele atoms) (.base a) T).toFun).rename
          (upTele (afterPairRenaming (Δ'.snoc Rt) X (.base a) T) (pairsTele atoms)).toFun =
          flatDelay left ((pairPastTele (Δ.snoc Rt) (unpackTele atoms) (.base a) T).comp
            (upTele (((ρ.up Rt).up (.base a)).up T) (unpackTele atoms))) :=
        (congrArg (fun t => LetCase.LocallyNameless.Tm.rename
            (upTele (afterPairRenaming (Δ'.snoc Rt) X (.base a) T) (pairsTele atoms)).toFun t)
          (flatDelay_rename left _ (pairPastTele ((Δ'.snoc Rt).snoc X) (pairsTele atoms) (.base a) T))).trans
          ((flatDelay_rename left _
            (upTele (afterPairRenaming (Δ'.snoc Rt) X (.base a) T) (pairsTele atoms))).trans
            (congrArg (flatDelay left)
              ((congrArg (fun r => BoundCtx.Renaming.comp
                  (((upTele ρ (Rt :: unpackTele atoms)).up (.base a)).up T) r)
                (pairPastTele_cons (pairsTele atoms) (Δ'.snoc Rt) X (.base a) T).symm).trans
                (pairPastTele_natural (unpackTele atoms) (ρ.up Rt) (.base a) T).symm)))
      exact step.trans (congrArg (unpackAt atoms 0) inner)
    have movedr : (flatTags right ((((ρ.up Rt).up Y).up (.base a)).up T)).rename afterPair =
        flatTags right ((afterPairRenaming (Δ.snoc Rt) Y (.base a) T).comp
          ((((ρ.up Rt).up (.base a)).up T).up Y)) :=
      (flatTags_rename right _ (afterPairRenaming (Δ'.snoc Rt) Y (.base a) T)).trans
        (congrArg (flatTags right) (afterPair_natural (ρ.up Rt) Y (.base a) T))
    have comm' := Eq.subst (motive := fun x => Equiv false Γ₀ (Δ'.snoc Rt)
      (.case (.bv 0)
        (.let₂ (.bv j.succ) (unpackAt atoms (2 : Fin (k + 4))
          ((flatDelay left (((upTele ρ (Rt :: unpackTele atoms)).up (.base a)).up T)).rename
            (pairPastTele ((Δ'.snoc Rt).snoc X) (pairsTele atoms) (.base a) T).toFun)))
        (.let₂ (.bv j.succ) (flatTags right ((((ρ.up Rt).up Y).up (.base a)).up T))))
      (.let₂ (.bv j) x) (packedExitType L))
      (congrArg₂ (LetCase.LocallyNameless.Tm.case (.bv 2)) movedl movedr) comm
    have renamed : (LetCase.LocallyNameless.Tm.case (.bv 0) (unpackAt atoms 0 l) r).rename (ρ.up Rt).toFun =
        .case (.bv 0) (unpackAt atoms 0 (l.rename (upTele ρ (Rt :: unpackTele atoms)).toFun))
          (r.rename ((ρ.up Rt).up Y).toFun) :=
      congrArg (fun x => LetCase.LocallyNameless.Tm.case (.bv 0) x (r.rename ((ρ.up Rt).up Y).toFun))
        (unpackAt_rename (Φ := Φ) atoms ((ρ.up Rt).up X) 0 l)
    exact Eq.subst (motive := fun x => Equiv false Γ₀ (Δ'.snoc Rt) x
      (.let₂ (.bv j)
        (flatTags (SpelledDelayTags.split atoms nxt more left right) (((ρ.up Rt).up (.base a)).up T)))
      (packedExitType L))
      renamed.symm ((Equiv.case (.refl (.bv (ι := (0 : Fin (k + 1))))) arml ihr).trans comm')

  | _, _, _, _, _, _, _, _, .keep _ _ _ kept, _, _, ρ => kept_comm kept (ρ.up _)

/-- The same for a subchain with a fresh tuple kept packed. The
destructuring of the older tuple also moves in front of the unpacking of
the fresh tuple. -/
theorem kept_comm : {a b : α} → {rest fresh : List α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {x : Slot Δ (tupleTy fresh)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ m} → (d : SpelledKept a b rest fresh Δ s x L t) → {k : Nat} →
    {Δ' : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming Δ Δ') →
    Equiv false Γ₀ Δ' (t.rename ρ.toFun)
      (.let₂ (.bv (ρ.toFun s.1)) (flatKept d ((ρ.up (.base a)).up (tupleTy (b :: rest)))))
      (packedExitType L)
  | a, b, rest, fresh, _, Δ, s, x, _, @SpelledKept.release _ _ _ _ _ _ _ _ _ _ _ _ body next, _, Δ', ρ => by
    let T : Ty α := tupleTy (b :: rest)
    have ih := delay_comm next (upTele ρ (pairsTele fresh))
    have slotAt : (upTele ρ (pairsTele fresh)).toFun ((weakenTele Δ (pairsTele fresh)).toFun s.1) =
        (weakenTele Δ' (pairsTele fresh)).toFun (ρ.toFun s.1) :=
      congrArg (fun r => r.toFun s.1) (weakenTele_natural (pairsTele fresh) ρ)
    have ih' : Equiv false Γ₀ (extendCtx Δ' (pairsTele fresh)) (body.rename (upTele ρ (pairsTele fresh)).toFun)
        (.let₂ (.bv ((weakenTele Δ' (pairsTele fresh)).toFun (ρ.toFun s.1)))
          (flatDelay next (((upTele ρ (pairsTele fresh)).up (.base a)).up T))) (packedExitType L) := by
      rw [← slotAt]
      exact ih
    have typed := flatDelay_typed next (((upTele ρ (pairsTele fresh)).up (.base a)).up T)
    have slot : Δ'.get (ρ.toFun s.1) = .product (.base a) T := (ρ.typed s.1).trans s.2
    have hx : Δ'.get (ρ.toFun x.1) = tupleTy fresh := (ρ.typed x.1).trans x.2
    have comm := unpack_pair_comm_proof fresh (Γ := Δ') (ρ.toFun x.1) (ρ.toFun s.1) hx slot typed
    have moved : (flatDelay next (((upTele ρ (pairsTele fresh)).up (.base a)).up T)).rename
        (pairPastTele Δ' (pairsTele fresh) (.base a) T).toFun =
        flatDelay next ((pairPastTele Δ (pairsTele fresh) (.base a) T).comp
          (upTele ((ρ.up (.base a)).up T) (pairsTele fresh))) :=
      (flatDelay_rename next _ (pairPastTele Δ' (pairsTele fresh) (.base a) T)).trans
        (congrArg (flatDelay next) (pairPastTele_natural (pairsTele fresh) ρ (.base a) T).symm)
    exact equiv_cast ((unpackAt_congr_proof fresh (Γ := Δ') (ρ.toFun x.1) hx ih').trans comm)
      (unpackAt_rename (Φ := Φ) fresh ρ x.1 body).symm
      (congrArg (fun z => LetCase.LocallyNameless.Tm.let₂ (.bv (ρ.toFun s.1)) (unpackAt fresh (ρ.toFun x.1).succ.succ z)) moved)
  | a, b, rest, _, _, Δ, s, _, _, .ask g argument reply, _, Δ', ρ => by
    let Rt : Ty α := tagsTy (replyTags g)
    let T : Ty α := tupleTy (b :: rest)
    have ih := keptTags_comm reply ρ
    have he : HasType Φ Γ₀ Δ' ((LetCase.LocallyNameless.Tm.op g (argTerm (Φ := Φ) argument)).rename ρ.toFun) Rt :=
      HasType.rename ρ (Derivation.op (f := g) (argTyping argument)).toHasType
    have typed := flatKeptTags_typed reply (((ρ.up Rt).up (.base a)).up T)
    have slot : Δ'.get (ρ.toFun s.1) = .product (.base a) T := (ρ.typed s.1).trans s.2
    have comm := let_pair_comm_proof (ρ.toFun s.1) slot he typed
    have request : ((LetCase.LocallyNameless.Tm.op g (argTerm (Φ := Φ) argument)).rename ρ.toFun).rename
        (fun i => i.succ.succ) =
        .op g ((argTerm argument).rename ((pastPair Δ (.base a) T).comp ((ρ.up (.base a)).up T)).toFun) := by
      simp only [LetCase.LocallyNameless.Tm.rename, LetCase.LocallyNameless.Tm.rename_comp]
      rfl
    have body : (flatKeptTags reply (((ρ.up Rt).up (.base a)).up T)).rename afterPair =
        flatKeptTags reply ((afterPairRenaming Δ Rt (.base a) T).comp (((ρ.up (.base a)).up T).up Rt)) :=
      (flatKeptTags_rename reply _ (afterPairRenaming Δ' Rt (.base a) T)).trans
        (congrArg (flatKeptTags reply) (afterPair_natural ρ Rt (.base a) T))
    have comm' := Eq.subst (motive := fun x => Equiv false Γ₀ Δ'
      (.let₁ ((LetCase.LocallyNameless.Tm.op g (argTerm (Φ := Φ) argument)).rename ρ.toFun)
        (.let₂ (.bv (ρ.toFun s.1).succ) (flatKeptTags reply (((ρ.up Rt).up (.base a)).up T))))
      (.let₂ (.bv (ρ.toFun s.1)) x) (packedExitType L))
      (congrArg₂ LetCase.LocallyNameless.Tm.let₁ request body) comm
    exact (Equiv.let₁ (.refl he) ih).trans comm'

/-- The same for the bound reply of a request of such a subchain, under its
slot. -/
theorem keptTags_comm : {a b : α} → {rest fresh : List α} → {tags : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {x : Slot Δ (tupleTy fresh)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → (d : SpelledKeptTags a b rest fresh tags Δ s x L t) → {k : Nat} →
    {Δ' : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming Δ Δ') →
    Equiv false Γ₀ (Δ'.snoc (tagsTy tags)) (t.rename (ρ.up (tagsTy tags)).toFun)
      (.let₂ (.bv (ρ.toFun s.1).succ)
        (flatKeptTags d (((ρ.up (tagsTy tags)).up (.base a)).up (tupleTy (b :: rest)))))
      (packedExitType L)
  | a, b, rest, _, _, _, Δ, s, _, _, @SpelledKeptTags.only _ _ _ _ _ _ _ _ _ _ _ _ atoms body next, _, Δ', ρ => by
    let X : Ty α := tupleTy atoms
    let T : Ty α := tupleTy (b :: rest)
    have ih := kept_comm next (upTele ρ (unpackTele atoms))
    have slotAt : (upTele ρ (unpackTele atoms)).toFun ((weakenTele Δ (unpackTele atoms)).toFun s.1) =
        (weakenTele (Δ'.snoc X) (pairsTele atoms)).toFun (ρ.toFun s.1).succ :=
      congrArg (fun r => r.toFun s.1) (weakenTele_natural (unpackTele atoms) ρ)
    have ih' : Equiv false Γ₀ (extendCtx (Δ'.snoc X) (pairsTele atoms))
        (body.rename (upTele ρ (unpackTele atoms)).toFun)
        (.let₂ (.bv ((weakenTele (Δ'.snoc X) (pairsTele atoms)).toFun (ρ.toFun s.1).succ))
          (flatKept next (((upTele ρ (unpackTele atoms)).up (.base a)).up T))) (packedExitType L) := by
      rw [← slotAt]
      exact ih
    have typed := flatKept_typed next (((upTele ρ (unpackTele atoms)).up (.base a)).up T)
    have slot : (Δ'.snoc X).get (ρ.toFun s.1).succ = .product (.base a) T := (ρ.typed s.1).trans s.2
    have comm := unpack_pair_comm_proof atoms (Γ := Δ'.snoc X) 0 (ρ.toFun s.1).succ rfl slot typed
    have moved : (flatKept next (((upTele ρ (unpackTele atoms)).up (.base a)).up T)).rename
        (pairPastTele (Δ'.snoc X) (pairsTele atoms) (.base a) T).toFun =
        flatKept next ((pairPastTele (Δ.snoc X) (pairsTele atoms) (.base a) T).comp
          (upTele (((ρ.up X).up (.base a)).up T) (pairsTele atoms))) :=
      (flatKept_rename next _ (pairPastTele (Δ'.snoc X) (pairsTele atoms) (.base a) T)).trans
        (congrArg (flatKept next) (pairPastTele_natural (pairsTele atoms) (ρ.up X) (.base a) T).symm)
    have comm' := Eq.subst (motive := fun x => Equiv false Γ₀ (Δ'.snoc X)
      (unpackAt atoms 0 (.let₂ (.bv ((weakenTele (Δ'.snoc X) (pairsTele atoms)).toFun (ρ.toFun s.1).succ))
        (flatKept next (((upTele ρ (unpackTele atoms)).up (.base a)).up T))))
      (.let₂ (.bv (ρ.toFun s.1).succ) (unpackAt atoms 2 x)) (packedExitType L)) moved comm
    have renamed : (unpackAt atoms 0 body).rename (ρ.up X).toFun =
        unpackAt atoms 0 (body.rename (upTele ρ (unpackTele atoms)).toFun) :=
      unpackAt_rename (Φ := Φ) atoms (ρ.up X) 0 body
    exact Eq.subst (motive := fun x => Equiv false Γ₀ (Δ'.snoc X) x
      (.let₂ (.bv (ρ.toFun s.1).succ)
        (flatKeptTags (SpelledKeptTags.only atoms next) (((ρ.up X).up (.base a)).up T))) (packedExitType L))
      renamed.symm ((unpackAt_congr_proof atoms (Γ := Δ'.snoc X) 0 rfl ih').trans comm')

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

omit [TaggedSignature α Φ] in
/-- Three renamings in a row are one. -/
theorem rename_three {k₀ k₁ k₂ k₃ : Nat} {Γ₀' : BoundCtx (Ty α) k₀} {Γ₁ : BoundCtx (Ty α) k₁}
    {Γ₂ : BoundCtx (Ty α) k₂} {Γ₃ : BoundCtx (Ty α) k₃} (t : LetCase.LocallyNameless.Tm Empty Φ k₀)
    (ρ₁ : BoundCtx.Renaming Γ₀' Γ₁) (ρ₂ : BoundCtx.Renaming Γ₁ Γ₂) (ρ₃ : BoundCtx.Renaming Γ₂ Γ₃) :
    ((t.rename ρ₁.toFun).rename ρ₂.toFun).rename ρ₃.toFun = t.rename ((ρ₁.comp ρ₂).comp ρ₃).toFun := by
  rw [LetCase.LocallyNameless.Tm.rename_comp, LetCase.LocallyNameless.Tm.rename_comp]
  rfl

omit [TaggedSignature α Φ] in
/-- Binding by a term is an action on terms that moves a pattern let on an
older pair slot to its front. -/
theorem let_frame_proof [HasTy Φ (Ty α)] {C : Ty α} {m : Nat} {Ω : BoundCtx (Ty α) m} {X : Ty α}
    (E : LetCase.LocallyNameless.Tm Empty Φ m) (hE : HasType Φ Γ₀ Ω E X) :
    PairFrame C Ω [X] (fun ω u => .let₁ (E.rename ω.toFun) u) where
  typed ω _ hu := .let₁ (HasType.rename ω hE) hu
  comm ω j A B hj body hBody := by
    have h := let_pair_comm_proof j hj (HasType.rename ω hE) hBody
    exact equiv_cast h rfl (congrArg (LetCase.LocallyNameless.Tm.let₂ (.bv j))
      (congrArg₂ LetCase.LocallyNameless.Tm.let₁ (LetCase.LocallyNameless.Tm.rename_comp _ _ E)
        (congrArg (fun r : BoundCtx.Renaming _ _ => body.rename r.toFun) (pairPastTele_single _ X A B).symm)))

omit [TaggedSignature α Φ] in
/-- Unpacking a tuple slot is an action on terms that moves a pattern let
on an older pair slot to its front. -/
theorem unpack_frame_proof [HasTy Φ (Ty α)] {C : Ty α} (atoms : List α) {m : Nat} {Ω : BoundCtx (Ty α) m} (i : Fin m)
    (h : Ω.get i = tupleTy atoms) :
    PairFrame (Φ := Φ) C Ω (pairsTele atoms) (fun ω u => unpackAt atoms (ω.toFun i) u) where
  typed ω _ hu := unpackAt_typed_proof atoms (ω.toFun i) ((ω.typed i).trans h) hu
  comm ω j _ _ hj _ hBody := unpack_pair_comm_proof atoms (ω.toFun i) j ((ω.typed i).trans h) hj hBody

/-- The unpacking of an older tuple slot moves in front of the unpacking of
the newest slot. -/
theorem unpack_unpack_proof {C : Ty α} (atoms H : List α) {m : Nat} {Ω : BoundCtx (Ty α) m} (j : Fin m)
    (hj : Ω.get j = tupleTy H)
    {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize (teleSize (m + 1) (pairsTele atoms)) (pairsTele H))}
    (hu : HasType Φ Γ₀ (extendCtx (extendCtx (Ω.snoc (tupleTy atoms)) (pairsTele atoms)) (pairsTele H)) u C) :
    Equiv false Γ₀ (Ω.snoc (tupleTy atoms))
      (unpackAt atoms 0
        (unpackAt H ((weakenTele (Ω.snoc (tupleTy atoms)) (pairsTele atoms)).toFun j.succ) u))
      (unpackAt H j.succ
        (unpackAt atoms ((weakenTele (Ω.snoc (tupleTy atoms)) (pairsTele H)).toFun 0)
          (u.rename (swapTeles (Ω.snoc (tupleTy atoms)) (pairsTele atoms) (pairsTele H)).toFun))) C :=
  unpack_out_proof (unpack_frame_proof atoms (Ω := Ω.snoc (tupleTy atoms)) 0 rfl) H
    (BoundCtx.Renaming.id _) j.succ hj hu

omit [TaggedSignature α Φ] in
/-- Renaming an unpacking whose slot is beneath a telescope so that the
slot is newest. -/
theorem unpack_swap_rename (atoms : List α) {k : Nat} (Ω : BoundCtx (Ty α) k) (X : Ty α) (P : List (Ty α))
    (v : LetCase.LocallyNameless.Tm Empty Φ (teleSize (teleSize (k + 1) P) (pairsTele atoms))) :
    (unpackAt atoms ((weakenTele (Ω.snoc X) P).toFun 0) v).rename (swapTeles Ω [X] P).toFun =
      unpackAt atoms (0 : Fin (teleSize k P + 1))
        (v.rename (upTele (swapTeles Ω [X] P) (pairsTele atoms)).toFun) :=
  (unpackAt_rename (Φ := Φ) atoms (swapTeles Ω [X] P) _ v).trans
    (congrArg (fun i => unpackAt atoms i (v.rename (upTele (swapTeles Ω [X] P) (pairsTele atoms)).toFun))
      (congrArg (fun r => r.toFun 0) (swapTeles_weaken P Ω X)))

omit [TaggedSignature α Φ] in
/-- Moving two slots beneath a telescope with one more oldest slot, after
placing that slot. -/
theorem arm_renaming {m k : Nat} {Δ : BoundCtx (Ty α) m} {Θ : BoundCtx (Ty α) k} (X A B : Ty α)
    (tel : List (Ty α)) (χ : BoundCtx.Renaming ((Δ.snoc A).snoc B) Θ) :
    (pairPastTele (Δ.snoc X) tel A B).comp (upTele ((afterPairRenaming Δ X A B).comp (χ.up X)) tel) =
      (pairPastTele Δ (X :: tel) A B).comp (upTele χ (X :: tel)) :=
  (congrArg (fun r => (pairPastTele (Δ.snoc X) tel A B).comp r) (upTele_comp tel _ _).symm).trans
    (congrArg (fun r => BoundCtx.Renaming.comp r (upTele χ (X :: tel))) (pairPastTele_cons tel Δ X A B).symm)

/-- The term of the normal form of a pending tuple is the unpacking around
the term of its body. -/
theorem SpelledTuple.normal_term : {n : Nat} → {β : BoundCtx (Ty α) n} → {atoms : List α} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → (d : SpelledTuple atoms β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → (ρ : BoundCtx.Renaming β γ) →
    (d.normal ρ).1 = unpackAt atoms 0 (d.opened ρ).1
  | _, _, _, _, .unit _, _, _, _ => rfl
  | _, _, _, _, .atom _ _, _, _, _ => rfl
  | _, _, _, _, .pair _ _ _ later, _, _, ρ =>
    congrArg (LetCase.LocallyNameless.Tm.let₂ (.bv 0)) (SpelledTuple.normal_term later ((ρ.up _).up _))
  | _, _, _, _, .hold _ _ _ _, _, _, _ => rfl

/-- The flattened continuation of an arm, with the first atom and the rest
of the held tuple moved beneath the slots of the arm. -/
theorem arm_flat {a b : α} {rest : List α} {m k : Nat} {Δ : BoundCtx (Ty α) m} {Θ : BoundCtx (Ty α) k}
    (tel : List (Ty α)) {s : Slot (extendCtx Δ tel) (tupleTy (a :: b :: rest))}
    {t : LetCase.LocallyNameless.Tm Empty Φ (teleSize m tel)} (next : SpelledDelay a b rest (extendCtx Δ tel) s L t)
    (σ : BoundCtx.Renaming Δ Θ)
    {N : LetCase.LocallyNameless.Tm Empty Φ (teleSize (teleSize k tel) (pairsTele (a :: b :: rest)))}
    (h : Equiv false Γ₀ (((extendCtx Θ tel).snoc (.base a)).snoc (tupleTy (b :: rest)))
      (flatDelay next (((upTele σ tel).up (.base a)).up (tupleTy (b :: rest))))
      (unpackAt (b :: rest) 0 N) (packedExitType L)) :
    Equiv false Γ₀ (extendCtx ((Θ.snoc (.base a)).snoc (tupleTy (b :: rest))) tel)
      (flatDelay next ((pairPastTele Δ tel (.base a) (tupleTy (b :: rest))).comp
        (upTele ((σ.up (.base a)).up (tupleTy (b :: rest))) tel)))
      (unpackAt (b :: rest) ((weakenTele ((Θ.snoc (.base a)).snoc (tupleTy (b :: rest))) tel).toFun 0)
        (N.rename (upTele (pairPastTele Θ tel (.base a) (tupleTy (b :: rest)))
          (pairsTele (b :: rest))).toFun))
      (packedExitType L) :=
  equiv_cast (h.rename (pairPastTele Θ tel (.base a) (tupleTy (b :: rest))))
    ((flatDelay_rename next _ (pairPastTele Θ tel (.base a) (tupleTy (b :: rest)))).trans
      (congrArg (flatDelay next) (pairPastTele_natural tel σ (.base a) (tupleTy (b :: rest))).symm))
    ((unpackAt_rename (Φ := Φ) (b :: rest) (pairPastTele Θ tel (.base a) (tupleTy (b :: rest))) 0 N).trans
      (congrArg (fun i => unpackAt (b :: rest) i (N.rename (upTele (pairPastTele Θ tel (.base a)
          (tupleTy (b :: rest))) (pairsTele (b :: rest))).toFun))
        (pairPastTele_zero tel Θ (.base a) (tupleTy (b :: rest)))))

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
    (delay_comm delay (ρ.up _)).trans (Equiv.let₂ (.refl .bv) (delay.opened_flat (ρ.up _)))

/-- The flattened chain, with the first atom and the rest of the tuple as
the two newest slots, is natively equal to unpacking the rest and then
running the body of the normal form. -/
theorem SpelledDelay.opened_flat : {a b : α} → {rest : List α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {t : LetCase.LocallyNameless.Tm Empty Φ m} →
    (d : SpelledDelay a b rest Δ s L t) → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    (σ : BoundCtx.Renaming Δ Θ) →
    Equiv false Γ₀ ((Θ.snoc (.base a)).snoc (tupleTy (b :: rest)))
      (flatDelay d ((σ.up (.base a)).up (tupleTy (b :: rest))))
      (unpackAt (b :: rest) 0 (d.opened σ).1) (packedExitType L)
  | _, _, _, _, _, _, _, .unpack later, _, _, σ =>
    equiv_cast (later.normal_equiv (σ.up _)) rfl (SpelledTuple.normal_term later (σ.up _))
  | a, b, rest, _, Δ, _, _, .ask g argument reply, _, Θ, σ => by
    let A : Ty α := .base a
    let T : Ty α := tupleTy (b :: rest)
    obtain ⟨U, hflat, hU, hopen⟩ := reply.opened_flat σ
    have hE : HasType Φ Γ₀ ((Θ.snoc A).snoc T)
        (.op g ((argTerm argument).rename ((pastPair Δ A T).comp ((σ.up A).up T)).toFun))
        (tagsTy (replyTags g)) :=
      HasType.rename ((pastPair Δ A T).comp ((σ.up A).up T))
        (Derivation.op (f := g) (argTyping argument)).toHasType
    have out := unpack_out_proof (let_frame_proof (C := packedExitType L) _ hE) (b :: rest)
      (BoundCtx.Renaming.id ((Θ.snoc A).snoc T)) 0 rfl hU
    have request : (LetCase.LocallyNameless.Tm.op g ((argTerm (Φ := Φ) argument).rename
        ((pastPair Δ A T).comp ((σ.up A).up T)).toFun)).rename
        ((BoundCtx.Renaming.id ((Θ.snoc A).snoc T)).comp
          (weakenTele ((Θ.snoc A).snoc T) (pairsTele (b :: rest)))).toFun =
        .op g (argTerm (argument.rename (σ.comp (weakenTele Θ (pairsTele (a :: b :: rest)))))) :=
      congrArg (LetCase.LocallyNameless.Tm.op g) ((LetCase.LocallyNameless.Tm.rename_comp _ _ (argTerm argument)).trans
        ((LetCase.LocallyNameless.Tm.rename_congr (fun _ => rfl) (argTerm argument)).trans
          (argTerm_rename argument (σ.comp (weakenTele Θ (pairsTele (a :: b :: rest)))))))
    exact (Equiv.let₁ (.refl hE) hflat).trans
      (equiv_cast out (congrArg (fun e => LetCase.LocallyNameless.Tm.let₁ e (unpackAt (b :: rest) 1 U)) (LetCase.LocallyNameless.Tm.rename_id _))
        (congrArg (unpackAt (b :: rest) 0) (congrArg₂ LetCase.LocallyNameless.Tm.let₁ request hopen)))

/-- The same for the bound reply of a request, under its slot. The body is
given with the reply slot beneath the unpacking of the rest of the tuple;
renamed so that the reply slot is newest it is the normal form of the
reply. -/
theorem SpelledDelayTags.opened_flat : {a b : α} → {rest : List α} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {s : Slot Δ (tupleTy (a :: b :: rest))} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} → (d : SpelledDelayTags a b rest tags Δ s L t) → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (σ : BoundCtx.Renaming Δ Θ) →
    ∃ U : LetCase.LocallyNameless.Tm Empty Φ (teleSize (k + 1 + 1 + 1) (pairsTele (b :: rest))),
      Equiv false Γ₀ (((Θ.snoc (.base a)).snoc (tupleTy (b :: rest))).snoc (tagsTy tags))
        (flatTags d ((afterPairRenaming Δ (tagsTy tags) (.base a) (tupleTy (b :: rest))).comp
          (((σ.up (.base a)).up (tupleTy (b :: rest))).up (tagsTy tags))))
        (unpackAt (b :: rest) 1 U) (packedExitType L) ∧
      HasType Φ Γ₀ (extendCtx (((Θ.snoc (.base a)).snoc (tupleTy (b :: rest))).snoc (tagsTy tags))
        (pairsTele (b :: rest))) U (packedExitType L) ∧
      U.rename (swapTeles ((Θ.snoc (.base a)).snoc (tupleTy (b :: rest))) [tagsTy tags]
        (pairsTele (b :: rest))).toFun = (d.opened σ).1
  | a, b, rest, _, _, Δ, _, _, .only atoms next, _, Θ, σ => by
    let A : Ty α := .base a
    let T : Ty α := tupleTy (b :: rest)
    let X : Ty α := tupleTy atoms
    have ih := next.opened_flat (upTele σ (unpackTele atoms))
    have hN := (next.opened (upTele σ (unpackTele atoms))).2.typing.toHasType
    have arm := arm_flat (unpackTele atoms) next σ ih
    have hu := HasType.rename (upTele (pairPastTele Θ (unpackTele atoms) A T) (pairsTele (b :: rest))) hN
    have out := unpack_unpack_proof atoms (b :: rest) (Ω := (Θ.snoc A).snoc T) 0 rfl hu
    refine ⟨_, (unpackAt_congr_proof atoms (Γ := ((Θ.snoc A).snoc T).snoc X) 0 rfl
        (equiv_cast arm (congrArg (flatDelay next)
          (arm_renaming X A T (pairsTele atoms) ((σ.up A).up T)).symm) rfl)).trans out,
      unpackAt_typed_proof atoms (Γ := extendCtx (((Θ.snoc A).snoc T).snoc X) (pairsTele (b :: rest))) _
        ((weakenTele (((Θ.snoc A).snoc T).snoc X) (pairsTele (b :: rest))).typed 0)
        (HasType.rename (swapTeles (((Θ.snoc A).snoc T).snoc X) (pairsTele atoms) (pairsTele (b :: rest))) hu),
      ?_⟩
    refine (unpack_swap_rename atoms ((Θ.snoc A).snoc T) X (pairsTele (b :: rest)) _).trans
      (congrArg (unpackAt atoms (0 : Fin (teleSize (_ + 1 + 1) (pairsTele (b :: rest)) + 1))) ?_)
    refine ((rename_three _ _ _ _).trans ?_).trans (CaseTree.renamed_body_term _ _).symm
    exact congrArg (fun r : BoundCtx.Renaming _ _ => LetCase.LocallyNameless.Tm.rename r.toFun _)
      ((congrArg (fun r => BoundCtx.Renaming.comp
          (upTele (pairPastTele Θ (unpackTele atoms) A T) (pairsTele (b :: rest))) r)
        (swapTeles_cons (pairsTele (b :: rest)) ((Θ.snoc A).snoc T) X (pairsTele atoms)).symm).trans
        (swapTeles_pair (pairsTele (b :: rest)) Θ (unpackTele atoms) A T).symm)
  | a, b, rest, _, _, Δ, _, _, .split atoms nxt more left right, k, Θ, σ => by
    let A : Ty α := .base a
    let T : Ty α := tupleTy (b :: rest)
    let Rt : Ty α := tagsTy (atoms :: nxt :: more)
    let X : Ty α := tupleTy atoms
    let Y : Ty α := tagsTy (nxt :: more)
    -- the first arm
    have ihl := left.opened_flat (upTele σ (Rt :: unpackTele atoms))
    have hNl := (left.opened (upTele σ (Rt :: unpackTele atoms))).2.typing.toHasType
    have arml := arm_flat (Rt :: unpackTele atoms) left σ ihl
    have hul := HasType.rename
      (upTele (pairPastTele Θ (Rt :: unpackTele atoms) A T) (pairsTele (b :: rest))) hNl
    have outl := unpack_unpack_proof atoms (b :: rest) (Ω := ((Θ.snoc A).snoc T).snoc Rt) 1 rfl hul
    have leftEq := (unpackAt_congr_proof atoms (Γ := (((Θ.snoc A).snoc T).snoc Rt).snoc X) 0 rfl
      (equiv_cast arml (congrArg (flatDelay left)
        (arm_renaming Rt A T (unpackTele atoms) ((σ.up A).up T)).symm) rfl)).trans outl
    have hl := unpackAt_typed_proof atoms
      (Γ := extendCtx ((((Θ.snoc A).snoc T).snoc Rt).snoc X) (pairsTele (b :: rest))) _
      ((weakenTele ((((Θ.snoc A).snoc T).snoc Rt).snoc X) (pairsTele (b :: rest))).typed 0)
      (HasType.rename (swapTeles ((((Θ.snoc A).snoc T).snoc Rt).snoc X) (pairsTele atoms)
        (pairsTele (b :: rest))) hul)
    -- the other arms
    obtain ⟨V, hflatR, hV, hopenR⟩ := right.opened_flat (σ.up Rt)
    have rightEq := equiv_cast (hflatR.rename ((afterPairRenaming Θ Rt A T).up Y))
      ((flatTags_rename right _ ((afterPairRenaming Θ Rt A T).up Y)).trans
        (congrArg (flatTags right)
          (congrArg (fun r => (afterPairRenaming (Δ.snoc Rt) Y A T).comp r)
            ((renaming_up_comp _ _ Y).trans
              (congrArg (fun r : BoundCtx.Renaming _ _ => r.up Y) (afterPair_natural σ Rt A T))))))
      (unpackAt_rename (Φ := Φ) (b :: rest) ((afterPairRenaming Θ Rt A T).up Y) 1 V)
    have hr := HasType.rename (upTele ((afterPairRenaming Θ Rt A T).up Y) (pairsTele (b :: rest))) hV
    -- the case
    have out := case_unpack_out_proof (C := packedExitType L) (b :: rest)
      (Γ := ((Θ.snoc A).snoc T).snoc Rt) (X := X) (Y := Y) 0 1 rfl rfl hl hr
    refine ⟨_, (Equiv.case (.refl (.bv (ι := (0 : Fin (k + 3))))) leftEq rightEq).trans out,
      .case (slot_typed _ ((weakenTele (((Θ.snoc A).snoc T).snoc Rt) (pairsTele (b :: rest))).typed 0))
        (HasType.rename (swapTeles (((Θ.snoc A).snoc T).snoc Rt) [X] (pairsTele (b :: rest))) hl)
        (HasType.rename (swapTeles (((Θ.snoc A).snoc T).snoc Rt) [Y] (pairsTele (b :: rest))) hr),
      ?_⟩
    have index : (swapTeles ((Θ.snoc A).snoc T) [Rt] (pairsTele (b :: rest))).toFun
        ((weakenTele (((Θ.snoc A).snoc T).snoc Rt) (pairsTele (b :: rest))).toFun 0) =
        (0 : Fin (teleSize (k + 1 + 1) (pairsTele (b :: rest)) + 1)) :=
      congrArg (fun r => r.toFun 0) (swapTeles_weaken (pairsTele (b :: rest)) ((Θ.snoc A).snoc T) Rt)
    show LetCase.LocallyNameless.Tm.case (.bv ((swapTeles ((Θ.snoc A).snoc T) [Rt] (pairsTele (b :: rest))).toFun
        ((weakenTele (((Θ.snoc A).snoc T).snoc Rt) (pairsTele (b :: rest))).toFun 0)))
      (LetCase.LocallyNameless.Tm.rename ((swapTeles ((Θ.snoc A).snoc T) [Rt] (pairsTele (b :: rest))).up X).toFun _)
      (LetCase.LocallyNameless.Tm.rename ((swapTeles ((Θ.snoc A).snoc T) [Rt] (pairsTele (b :: rest))).up Y).toFun _) = _
    refine congr (congr (congrArg (fun i => LetCase.LocallyNameless.Tm.case (.bv i)) index) ?_) ?_
    · -- the first arm of the normal form
      have c1 := swapTeles_cons (pairsTele (b :: rest)) (((Θ.snoc A).snoc T).snoc Rt) X (pairsTele atoms)
      have c2 := swapTeles_cons (pairsTele (b :: rest)) ((Θ.snoc A).snoc T) Rt (X :: pairsTele atoms)
      have c3 := swapTeles_pair (pairsTele (b :: rest)) Θ (Rt :: unpackTele atoms) A T
      refine ((congrArg (fun t => LetCase.LocallyNameless.Tm.rename
            ((swapTeles ((Θ.snoc A).snoc T) [Rt] (pairsTele (b :: rest))).up X).toFun t)
          (unpack_swap_rename atoms (((Θ.snoc A).snoc T).snoc Rt) X (pairsTele (b :: rest)) _)).trans
        (unpackAt_rename (Φ := Φ) atoms
          ((swapTeles ((Θ.snoc A).snoc T) [Rt] (pairsTele (b :: rest))).up X) 0 _)).trans
        (congrArg (unpackAt atoms (0 : Fin (teleSize (k + 1 + 1) (pairsTele (b :: rest)) + 1 + 1))) ?_)
      refine ((congrArg (fun t => LetCase.LocallyNameless.Tm.rename (upTele ((swapTeles ((Θ.snoc A).snoc T) [Rt]
            (pairsTele (b :: rest))).up X) (pairsTele atoms)).toFun t) (rename_three _ _ _ _)).trans
          ((LetCase.LocallyNameless.Tm.rename_comp _ _ _).trans ?_)).trans (CaseTree.renamed_body_term _ _).symm
      exact congrArg (fun r : BoundCtx.Renaming _ _ => LetCase.LocallyNameless.Tm.rename r.toFun _)
        (c3.trans (congrArg (fun r => BoundCtx.Renaming.comp
            (upTele (pairPastTele Θ (Rt :: unpackTele atoms) A T) (pairsTele (b :: rest))) r)
          (c2.trans (congrArg (fun r => BoundCtx.Renaming.comp r
            (upTele (swapTeles ((Θ.snoc A).snoc T) [Rt] (pairsTele (b :: rest))) (X :: pairsTele atoms)))
            c1)))).symm
    · -- the other arms of the normal form
      have nat := swapTeles_natural (pairsTele (b :: rest)) [Y] (afterPairRenaming Θ Rt A T)
      have inner : (upTele (afterPairRenaming Θ Rt A T) (pairsTele (b :: rest))).comp
          (swapTeles ((Θ.snoc A).snoc T) [Rt] (pairsTele (b :: rest))) =
          swapTeles Θ [Rt] (A :: T :: pairsTele (b :: rest)) :=
        (congrArg (fun r => BoundCtx.Renaming.comp (upTele r (pairsTele (b :: rest)))
            (swapTeles ((Θ.snoc A).snoc T) [Rt] (pairsTele (b :: rest))))
          (pairPastTele_single Θ Rt A T).symm).trans
          (swapTeles_pair (pairsTele (b :: rest)) Θ [Rt] A T).symm
      have lifted : ((upTele (afterPairRenaming Θ Rt A T) (pairsTele (b :: rest))).up Y).comp
          ((swapTeles ((Θ.snoc A).snoc T) [Rt] (pairsTele (b :: rest))).up Y) =
          (swapTeles Θ [Rt] (A :: T :: pairsTele (b :: rest))).up Y :=
        (renaming_up_comp _ _ Y).trans (congrArg (fun r : BoundCtx.Renaming _ _ => r.up Y) inner)
      have renamedTags : (CaseTree.renamed (pending := .tags (nxt :: more))
          (β := (extendCtx (Θ.snoc Rt) (pairsTele (a :: b :: rest))).snoc Y)
          (right.opened (σ.up Rt)).2 (swapTeles Θ [Rt] (pairsTele (a :: b :: rest)))).1 =
          (right.opened (σ.up Rt)).1.rename
            (LetCase.LocallyNameless.Tm.up (swapTeles Θ [Rt] (pairsTele (a :: b :: rest))).toFun) :=
        CaseTree.renamed_term (right.opened (σ.up Rt)).2 (swapTeles Θ [Rt] (pairsTele (a :: b :: rest)))
      exact (rename_three V _ _ _).trans
        ((congrArg (fun r : BoundCtx.Renaming _ _ => V.rename r.toFun)
          ((congrArg (fun r => BoundCtx.Renaming.comp r
              ((swapTeles ((Θ.snoc A).snoc T) [Rt] (pairsTele (b :: rest))).up Y)) nat.symm).trans
            (congrArg (fun r => BoundCtx.Renaming.comp
              (swapTeles (((Θ.snoc Rt).snoc A).snoc T) [Y] (pairsTele (b :: rest))) r) lifted))).trans
          ((LetCase.LocallyNameless.Tm.rename_comp
              (swapTeles (((Θ.snoc Rt).snoc A).snoc T) [Y] (pairsTele (b :: rest))).toFun
              ((swapTeles Θ [Rt] (pairsTele (a :: b :: rest))).up Y).toFun V).symm.trans
            ((congrArg (fun t => LetCase.LocallyNameless.Tm.rename
                ((swapTeles Θ [Rt] (pairsTele (a :: b :: rest))).up Y).toFun t) hopenR).trans
              renamedTags.symm)))

  | a, b, rest, _, _, Δ, _, _, .keep c d more kept, k, Θ, σ => by
    let A : Ty α := .base a
    let T : Ty α := tupleTy (b :: rest)
    let X : Ty α := tupleTy (c :: d :: more)
    have ih := kept.opened_flat (σ.up X)
    have hN := (kept.opened (σ.up X)).2.typing.toHasType
    have index : (upTele (afterPairRenaming Θ X A T) (pairsTele (b :: rest))).toFun
        ((weakenTele (((Θ.snoc X).snoc A).snoc T) (pairsTele (b :: rest))).toFun 2) =
        (weakenTele (((Θ.snoc A).snoc T).snoc X) (pairsTele (b :: rest))).toFun 0 :=
      congrArg (fun r => r.toFun 2) (weakenTele_natural (pairsTele (b :: rest)) (afterPairRenaming Θ X A T))
    have armEq := equiv_cast (ih.rename (afterPairRenaming Θ X A T))
      ((flatKept_rename kept _ (afterPairRenaming Θ X A T)).trans
        (congrArg (flatKept kept) (afterPair_natural σ X A T)))
      ((unpackAt_rename (Φ := Φ) (b :: rest) (afterPairRenaming Θ X A T) 0 _).trans
        (congrArg (unpackAt (b :: rest) (1 : Fin (k + 3)))
          ((unpackAt_rename (Φ := Φ) (c :: d :: more)
              (upTele (afterPairRenaming Θ X A T) (pairsTele (b :: rest))) _ _).trans
            (congrArg (fun i => unpackAt (c :: d :: more) i
              ((kept.opened (σ.up X)).1.rename (upTele (upTele (afterPairRenaming Θ X A T)
                (pairsTele (b :: rest))) (pairsTele (c :: d :: more))).toFun)) index))))
    refine ⟨_, armEq,
      unpackAt_typed_proof (c :: d :: more)
        (Γ := extendCtx (((Θ.snoc A).snoc T).snoc X) (pairsTele (b :: rest))) _
        ((weakenTele (((Θ.snoc A).snoc T).snoc X) (pairsTele (b :: rest))).typed 0)
        (HasType.rename (upTele (upTele (afterPairRenaming Θ X A T) (pairsTele (b :: rest)))
          (pairsTele (c :: d :: more))) hN), ?_⟩
    refine (unpack_swap_rename (c :: d :: more) ((Θ.snoc A).snoc T) X (pairsTele (b :: rest)) _).trans
      (congrArg (unpackAt (c :: d :: more) (0 : Fin (teleSize (k + 1 + 1) (pairsTele (b :: rest)) + 1))) ?_)
    refine ((LetCase.LocallyNameless.Tm.rename_comp _ _ _).trans ?_).trans (CaseTree.renamed_body_term _ _).symm
    exact congrArg (fun r : BoundCtx.Renaming _ _ => LetCase.LocallyNameless.Tm.rename r.toFun _)
      ((upTele_comp (pairsTele (c :: d :: more)) _ _).trans
        (congrArg (fun r => upTele r (pairsTele (c :: d :: more)))
          ((congrArg (fun r => BoundCtx.Renaming.comp (upTele r (pairsTele (b :: rest)))
              (swapTeles ((Θ.snoc A).snoc T) [X] (pairsTele (b :: rest))))
            (pairPastTele_single Θ X A T).symm).trans
            (swapTeles_pair (pairsTele (b :: rest)) Θ [X] A T).symm)))

/-- The same for a subchain with a fresh tuple kept packed: the flattened
subchain is natively equal to unpacking the rest of the older tuple, then
the fresh tuple, and then running the body of the normal form. -/
theorem SpelledKept.opened_flat : {a b : α} → {rest fresh : List α} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {x : Slot Δ (tupleTy fresh)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ m} → (d : SpelledKept a b rest fresh Δ s x L t) → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → (σ : BoundCtx.Renaming Δ Θ) →
    Equiv false Γ₀ ((Θ.snoc (.base a)).snoc (tupleTy (b :: rest)))
      (flatKept d ((σ.up (.base a)).up (tupleTy (b :: rest))))
      (unpackAt (b :: rest) 0 (unpackAt fresh
        ((weakenTele ((Θ.snoc (.base a)).snoc (tupleTy (b :: rest))) (pairsTele (b :: rest))).toFun
          (σ.toFun x.1).succ.succ) (d.opened σ).1)) (packedExitType L)
  | a, b, rest, fresh, _, Δ, _, x, _, .release next, k, Θ, σ => by
    let A : Ty α := .base a
    let T : Ty α := tupleTy (b :: rest)
    have ih := next.opened_flat (upTele σ (pairsTele fresh))
    have hN := (next.opened (upTele σ (pairsTele fresh))).2.typing.toHasType
    have arm := arm_flat (pairsTele fresh) next σ ih
    have hu := HasType.rename (upTele (pairPastTele Θ (pairsTele fresh) A T) (pairsTele (b :: rest))) hN
    have hx : ((Θ.snoc A).snoc T).get (σ.toFun x.1).succ.succ = tupleTy fresh := (σ.typed x.1).trans x.2
    have out := unpack_out_proof (unpack_frame_proof (C := packedExitType L) fresh
      (Ω := (Θ.snoc A).snoc T) (σ.toFun x.1).succ.succ hx) (b :: rest)
      (BoundCtx.Renaming.id ((Θ.snoc A).snoc T)) 0 rfl hu
    exact (unpackAt_congr_proof fresh (Γ := (Θ.snoc A).snoc T) (σ.toFun x.1).succ.succ hx arm).trans
      (equiv_cast out rfl (congrArg (fun z => unpackAt (b :: rest) (0 : Fin (k + 2)) (unpackAt fresh
          ((weakenTele ((Θ.snoc A).snoc T) (pairsTele (b :: rest))).toFun (σ.toFun x.1).succ.succ) z))
        (((LetCase.LocallyNameless.Tm.rename_comp (upTele (pairPastTele Θ (pairsTele fresh) A T) (pairsTele (b :: rest))).toFun
            (swapTeles ((Θ.snoc A).snoc T) (pairsTele fresh) (pairsTele (b :: rest))).toFun
            (next.opened (upTele σ (pairsTele fresh))).1).trans
          (congrArg (fun r : BoundCtx.Renaming _ _ => LetCase.LocallyNameless.Tm.rename r.toFun
              (next.opened (upTele σ (pairsTele fresh))).1)
            (swapTeles_pair (pairsTele (b :: rest)) Θ (pairsTele fresh) A T).symm)).trans
          (CaseTree.renamed_body_term (next.opened (upTele σ (pairsTele fresh))).2
            (swapTeles Θ (pairsTele fresh) (pairsTele (a :: b :: rest)))).symm)))
  | a, b, rest, fresh, _, Δ, _, x, _, .ask g argument reply, k, Θ, σ => by
    let A : Ty α := .base a
    let T : Ty α := tupleTy (b :: rest)
    let Rt : Ty α := tagsTy (replyTags g)
    obtain ⟨U, hflat, hU, hopen⟩ := reply.opened_flat σ
    have hx : ((Θ.snoc A).snoc T).get (σ.toFun x.1).succ.succ = tupleTy fresh := (σ.typed x.1).trans x.2
    have hE : HasType Φ Γ₀ ((Θ.snoc A).snoc T)
        (.op g ((argTerm argument).rename ((pastPair Δ A T).comp ((σ.up A).up T)).toFun)) Rt :=
      HasType.rename ((pastPair Δ A T).comp ((σ.up A).up T))
        (Derivation.op (f := g) (argTyping argument)).toHasType
    have hV := unpackAt_typed_proof fresh
      (Γ := extendCtx (((Θ.snoc A).snoc T).snoc Rt) (pairsTele (b :: rest))) _
      (((weakenTele (((Θ.snoc A).snoc T).snoc Rt) (pairsTele (b :: rest))).typed
        (σ.toFun x.1).succ.succ.succ).trans hx) hU
    have out₁ := unpack_out_proof (let_frame_proof (C := packedExitType L) _ hE) (b :: rest)
      (BoundCtx.Renaming.id ((Θ.snoc A).snoc T)) 0 rfl hV
    have moved := (unpackAt_rename (Φ := Φ) fresh
        (swapTeles ((Θ.snoc A).snoc T) [Rt] (pairsTele (b :: rest))) _ U).trans
      (congrArg (fun i => unpackAt fresh i (U.rename (upTele (swapTeles ((Θ.snoc A).snoc T) [Rt]
          (pairsTele (b :: rest))) (pairsTele fresh)).toFun))
        (congrArg (fun r => r.toFun (σ.toFun x.1).succ.succ.succ)
          (swapTeles_weaken (pairsTele (b :: rest)) ((Θ.snoc A).snoc T) Rt)))
    have hE₂ := HasType.rename ((BoundCtx.Renaming.id ((Θ.snoc A).snoc T)).comp
      (weakenTele ((Θ.snoc A).snoc T) (pairsTele (b :: rest)))) hE
    have hU₂ := HasType.rename (upTele (swapTeles ((Θ.snoc A).snoc T) [Rt] (pairsTele (b :: rest)))
      (pairsTele fresh)) hU
    have hx₂ : (extendCtx ((Θ.snoc A).snoc T) (pairsTele (b :: rest))).get
        ((weakenTele ((Θ.snoc A).snoc T) (pairsTele (b :: rest))).toFun (σ.toFun x.1).succ.succ) =
        tupleTy fresh :=
      ((weakenTele ((Θ.snoc A).snoc T) (pairsTele (b :: rest))).typed (σ.toFun x.1).succ.succ).trans hx
    have out₂ := unpack_out_proof (let_frame_proof (C := packedExitType L) _ hE₂) fresh
      (BoundCtx.Renaming.id (extendCtx ((Θ.snoc A).snoc T) (pairsTele (b :: rest))))
      ((weakenTele ((Θ.snoc A).snoc T) (pairsTele (b :: rest))).toFun (σ.toFun x.1).succ.succ) hx₂ hU₂
    have request : ((LetCase.LocallyNameless.Tm.op g ((argTerm (Φ := Φ) argument).rename
        ((pastPair Δ A T).comp ((σ.up A).up T)).toFun)).rename
        ((BoundCtx.Renaming.id ((Θ.snoc A).snoc T)).comp
          (weakenTele ((Θ.snoc A).snoc T) (pairsTele (b :: rest)))).toFun).rename
        ((BoundCtx.Renaming.id (extendCtx ((Θ.snoc A).snoc T) (pairsTele (b :: rest)))).comp
          (weakenTele (extendCtx ((Θ.snoc A).snoc T) (pairsTele (b :: rest))) (pairsTele fresh))).toFun =
        .op g (argTerm (argument.rename ((σ.comp (weakenTele Θ (pairsTele (a :: b :: rest)))).comp
          (weakenTele (extendCtx Θ (pairsTele (a :: b :: rest))) (pairsTele fresh))))) :=
      congrArg (LetCase.LocallyNameless.Tm.op g)
        ((congrArg (fun t => LetCase.LocallyNameless.Tm.rename
            ((BoundCtx.Renaming.id (extendCtx ((Θ.snoc A).snoc T) (pairsTele (b :: rest)))).comp
              (weakenTele (extendCtx ((Θ.snoc A).snoc T) (pairsTele (b :: rest))) (pairsTele fresh))).toFun t)
          (LetCase.LocallyNameless.Tm.rename_comp _ _ (argTerm argument))).trans
          ((LetCase.LocallyNameless.Tm.rename_comp _ _ (argTerm argument)).trans
            ((LetCase.LocallyNameless.Tm.rename_congr (fun _ => rfl) (argTerm argument)).trans
              (argTerm_rename argument ((σ.comp (weakenTele Θ (pairsTele (a :: b :: rest)))).comp
                (weakenTele (extendCtx Θ (pairsTele (a :: b :: rest))) (pairsTele fresh)))))))
    exact (Equiv.let₁ (.refl hE) hflat).trans
      ((equiv_cast out₁ (congrArg (fun e => LetCase.LocallyNameless.Tm.let₁ e (unpackAt (b :: rest) 1 (unpackAt fresh
            ((weakenTele (((Θ.snoc A).snoc T).snoc Rt) (pairsTele (b :: rest))).toFun
              (σ.toFun x.1).succ.succ.succ) U))) (LetCase.LocallyNameless.Tm.rename_id _))
          (congrArg (fun z => unpackAt (b :: rest) (0 : Fin (k + 2)) (LetCase.LocallyNameless.Tm.let₁ _ z)) moved)).trans
        (unpackAt_congr_proof (b :: rest) (Γ := (Θ.snoc A).snoc T) 0 rfl
          (equiv_cast out₂ (congrArg (fun e => LetCase.LocallyNameless.Tm.let₁ e _) (LetCase.LocallyNameless.Tm.rename_id _))
            (congrArg (unpackAt fresh ((weakenTele ((Θ.snoc A).snoc T) (pairsTele (b :: rest))).toFun
                (σ.toFun x.1).succ.succ))
              (congrArg₂ LetCase.LocallyNameless.Tm.let₁ request ((LetCase.LocallyNameless.Tm.rename_comp _ _ U).trans hopen))))))

/-- The same for the bound reply of a request of such a subchain, under its
slot. -/
theorem SpelledKeptTags.opened_flat : {a b : α} → {rest fresh : List α} → {tags : List (List α)} →
    {m : Nat} → {Δ : BoundCtx (Ty α) m} → {s : Slot Δ (tupleTy (a :: b :: rest))} →
    {x : Slot Δ (tupleTy fresh)} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} →
    (d : SpelledKeptTags a b rest fresh tags Δ s x L t) → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    (σ : BoundCtx.Renaming Δ Θ) →
    ∃ U : LetCase.LocallyNameless.Tm Empty Φ (teleSize (teleSize (k + 1 + 1 + 1) (pairsTele (b :: rest))) (pairsTele fresh)),
      Equiv false Γ₀ (((Θ.snoc (.base a)).snoc (tupleTy (b :: rest))).snoc (tagsTy tags))
        (flatKeptTags d ((afterPairRenaming Δ (tagsTy tags) (.base a) (tupleTy (b :: rest))).comp
          (((σ.up (.base a)).up (tupleTy (b :: rest))).up (tagsTy tags))))
        (unpackAt (b :: rest) 1 (unpackAt fresh
          ((weakenTele (((Θ.snoc (.base a)).snoc (tupleTy (b :: rest))).snoc (tagsTy tags))
            (pairsTele (b :: rest))).toFun (σ.toFun x.1).succ.succ.succ) U)) (packedExitType L) ∧
      HasType Φ Γ₀ (extendCtx (extendCtx (((Θ.snoc (.base a)).snoc (tupleTy (b :: rest))).snoc (tagsTy tags))
        (pairsTele (b :: rest))) (pairsTele fresh)) U (packedExitType L) ∧
      U.rename ((upTele (swapTeles ((Θ.snoc (.base a)).snoc (tupleTy (b :: rest))) [tagsTy tags]
          (pairsTele (b :: rest))) (pairsTele fresh)).comp
        (swapTeles (extendCtx ((Θ.snoc (.base a)).snoc (tupleTy (b :: rest))) (pairsTele (b :: rest)))
          [tagsTy tags] (pairsTele fresh))).toFun = (d.opened σ).1
  | a, b, rest, fresh, _, _, Δ, _, x, _, .only atoms next, k, Θ, σ => by
    let A : Ty α := .base a
    let T : Ty α := tupleTy (b :: rest)
    let Xh : Ty α := tupleTy atoms
    let Γ := (Θ.snoc A).snoc T
    let pp := pairPastTele Θ (unpackTele atoms) A T
    let Ω₂ := extendCtx (Γ.snoc Xh) (pairsTele (b :: rest))
    let s₁ := swapTeles Γ [Xh] (pairsTele (b :: rest))
    have hx : Γ.get (σ.toFun x.1).succ.succ = tupleTy fresh := (σ.typed x.1).trans x.2
    have ih := next.opened_flat (upTele σ (unpackTele atoms))
    have hN := (next.opened (upTele σ (unpackTele atoms))).2.typing.toHasType
    -- rename the equation of the continuation so that the first atom and the rest are beneath the reply
    have index₁ : (upTele pp (pairsTele (b :: rest))).toFun
        ((weakenTele (((extendCtx Θ (unpackTele atoms)).snoc A).snoc T) (pairsTele (b :: rest))).toFun
          ((upTele σ (unpackTele atoms)).toFun ((weakenTele Δ (unpackTele atoms)).toFun x.1)).succ.succ) =
        (weakenTele (extendCtx (Γ.snoc Xh) (pairsTele atoms)) (pairsTele (b :: rest))).toFun
          ((weakenTele (Γ.snoc Xh) (pairsTele atoms)).toFun (σ.toFun x.1).succ.succ.succ) :=
      (congrArg (fun r => r.toFun ((upTele σ (unpackTele atoms)).toFun
          ((weakenTele Δ (unpackTele atoms)).toFun x.1)).succ.succ)
        (weakenTele_natural (pairsTele (b :: rest)) pp)).trans
        (congrArg (weakenTele (extendCtx Γ (unpackTele atoms)) (pairsTele (b :: rest))).toFun
          ((congrArg (fun y => pp.toFun y.succ.succ)
            (congrArg (fun r => r.toFun x.1) (weakenTele_natural (unpackTele atoms) σ))).trans
            (congrArg (fun r => r.toFun (σ.toFun x.1).succ.succ)
              (pairPastTele_weaken (unpackTele atoms) Θ A T))))
    have armEq := equiv_cast (ih.rename pp)
      ((flatKept_rename next _ pp).trans (congrArg (flatKept next)
        ((pairPastTele_natural (unpackTele atoms) σ A T).symm.trans
          (arm_renaming Xh A T (pairsTele atoms) ((σ.up A).up T)).symm)))
      ((unpackAt_rename (Φ := Φ) (b :: rest) pp 0 _).trans
        (congrArg₂ (fun i z => unpackAt (b :: rest) i z) (pairPastTele_zero (unpackTele atoms) Θ A T)
          ((unpackAt_rename (Φ := Φ) fresh (upTele pp (pairsTele (b :: rest))) _ _).trans
            (congrArg (fun i => unpackAt fresh i ((next.opened (upTele σ (unpackTele atoms))).1.rename
              (upTele (upTele pp (pairsTele (b :: rest))) (pairsTele fresh)).toFun)) index₁))))
    have hN₂ := HasType.rename (upTele (upTele pp (pairsTele (b :: rest))) (pairsTele fresh)) hN
    have hV := unpackAt_typed_proof fresh
      (Γ := extendCtx (extendCtx (Γ.snoc Xh) (pairsTele atoms)) (pairsTele (b :: rest))) _
      (((weakenTele (extendCtx (Γ.snoc Xh) (pairsTele atoms)) (pairsTele (b :: rest))).typed _).trans
        (((weakenTele (Γ.snoc Xh) (pairsTele atoms)).typed (σ.toFun x.1).succ.succ.succ).trans hx)) hN₂
    -- move the unpacking of the rest of the older tuple in front of the unpacking of the reply
    have out₁ := unpack_unpack_proof atoms (b :: rest) (Ω := Γ) 0 rfl hV
    have moved := (unpackAt_rename (Φ := Φ) fresh
        (swapTeles (Γ.snoc Xh) (pairsTele atoms) (pairsTele (b :: rest))) _ _).trans
      (congrArg (fun i => unpackAt fresh i
          (((next.opened (upTele σ (unpackTele atoms))).1.rename
            (upTele (upTele pp (pairsTele (b :: rest))) (pairsTele fresh)).toFun).rename
            (upTele (swapTeles (Γ.snoc Xh) (pairsTele atoms) (pairsTele (b :: rest))) (pairsTele fresh)).toFun))
        (congrArg (fun r => r.toFun (σ.toFun x.1).succ.succ.succ)
          (swapTeles_weakenTele (pairsTele (b :: rest)) (Γ.snoc Xh) (pairsTele atoms))))
    -- move the unpacking of the fresh tuple in front of the unpacking of the reply
    have hW := HasType.rename (upTele (swapTeles (Γ.snoc Xh) (pairsTele atoms) (pairsTele (b :: rest)))
      (pairsTele fresh)) hN₂
    have hx₂ : Ω₂.get ((weakenTele (Γ.snoc Xh) (pairsTele (b :: rest))).toFun (σ.toFun x.1).succ.succ.succ) =
        tupleTy fresh :=
      ((weakenTele (Γ.snoc Xh) (pairsTele (b :: rest))).typed (σ.toFun x.1).succ.succ.succ).trans hx
    have out₂ := unpack_out_proof (unpack_frame_proof (C := packedExitType L) atoms (Ω := Ω₂)
        ((weakenTele (Γ.snoc Xh) (pairsTele (b :: rest))).toFun 0)
        ((weakenTele (Γ.snoc Xh) (pairsTele (b :: rest))).typed 0)) fresh (BoundCtx.Renaming.id Ω₂)
      ((weakenTele (Γ.snoc Xh) (pairsTele (b :: rest))).toFun (σ.toFun x.1).succ.succ.succ) hx₂ hW
    refine ⟨_, (unpackAt_congr_proof atoms (Γ := Γ.snoc Xh) 0 rfl armEq).trans
        ((equiv_cast out₁ rfl (congrArg (fun z => unpackAt (b :: rest) (1 : Fin (k + 3))
            (unpackAt atoms ((weakenTele (Γ.snoc Xh) (pairsTele (b :: rest))).toFun 0) z)) moved)).trans
          (unpackAt_congr_proof (b :: rest) (Γ := Γ.snoc Xh) 1 rfl out₂)),
      unpackAt_typed_proof atoms (Γ := extendCtx Ω₂ (pairsTele fresh)) _
        (((weakenTele Ω₂ (pairsTele fresh)).typed _).trans
          ((weakenTele (Γ.snoc Xh) (pairsTele (b :: rest))).typed 0))
        (HasType.rename (swapTeles Ω₂ (pairsTele atoms) (pairsTele fresh)) hW), ?_⟩
    -- the body of the normal form
    have i₁ : (upTele s₁ (pairsTele fresh)).toFun
        ((weakenTele Ω₂ (pairsTele fresh)).toFun ((weakenTele (Γ.snoc Xh) (pairsTele (b :: rest))).toFun 0)) =
        (weakenTele ((extendCtx Γ (pairsTele (b :: rest))).snoc Xh) (pairsTele fresh)).toFun
          (s₁.toFun ((weakenTele (Γ.snoc Xh) (pairsTele (b :: rest))).toFun 0)) :=
      congrArg (fun r : BoundCtx.Renaming Ω₂ _ =>
        r.toFun ((weakenTele (Γ.snoc Xh) (pairsTele (b :: rest))).toFun 0))
        (weakenTele_natural (pairsTele fresh) s₁)
    have i₂ : s₁.toFun ((weakenTele (Γ.snoc Xh) (pairsTele (b :: rest))).toFun 0) =
        (0 : Fin (teleSize (k + 1 + 1) (pairsTele (b :: rest)) + 1)) :=
      congrArg (fun r : BoundCtx.Renaming (Γ.snoc Xh) _ => r.toFun 0)
        (swapTeles_weaken (pairsTele (b :: rest)) Γ Xh)
    have i₃ : (swapTeles (extendCtx Γ (pairsTele (b :: rest))) [Xh] (pairsTele fresh)).toFun
        ((weakenTele ((extendCtx Γ (pairsTele (b :: rest))).snoc Xh) (pairsTele fresh)).toFun 0) =
        (0 : Fin (teleSize (teleSize (k + 1 + 1) (pairsTele (b :: rest))) (pairsTele fresh) + 1)) :=
      congrArg (fun r : BoundCtx.Renaming ((extendCtx Γ (pairsTele (b :: rest))).snoc Xh) _ => r.toFun 0)
        (swapTeles_weaken (pairsTele fresh) (extendCtx Γ (pairsTele (b :: rest))) Xh)
    have index₂ : ((upTele s₁ (pairsTele fresh)).comp
        (swapTeles (extendCtx Γ (pairsTele (b :: rest))) [Xh] (pairsTele fresh))).toFun
        ((weakenTele Ω₂ (pairsTele fresh)).toFun ((weakenTele (Γ.snoc Xh) (pairsTele (b :: rest))).toFun 0)) =
        (0 : Fin (teleSize (teleSize (k + 1 + 1) (pairsTele (b :: rest))) (pairsTele fresh) + 1)) :=
      (congrArg (swapTeles (extendCtx Γ (pairsTele (b :: rest))) [Xh] (pairsTele fresh)).toFun
        (i₁.trans (congrArg (weakenTele ((extendCtx Γ (pairsTele (b :: rest))).snoc Xh)
          (pairsTele fresh)).toFun i₂))).trans i₃
    have e₁ : swapTeles Θ (unpackTele atoms) (A :: T :: pairsTele (b :: rest)) =
        ((upTele pp (pairsTele (b :: rest))).comp
          (swapTeles (Γ.snoc Xh) (pairsTele atoms) (pairsTele (b :: rest)))).comp (upTele s₁ (pairsTele atoms)) :=
      (swapTeles_pair (pairsTele (b :: rest)) Θ (unpackTele atoms) A T).trans
        (congrArg (fun r => BoundCtx.Renaming.comp (upTele pp (pairsTele (b :: rest))) r)
          (swapTeles_cons (pairsTele (b :: rest)) Γ Xh (pairsTele atoms)))
    have e₂ := swapTeles_cons (pairsTele fresh) (extendCtx Γ (pairsTele (b :: rest))) Xh (pairsTele atoms)
    have nat := swapTeles_natural (pairsTele fresh) (pairsTele atoms) s₁
    have total : (((upTele ((upTele pp (pairsTele (b :: rest))).comp
          (swapTeles (Γ.snoc Xh) (pairsTele atoms) (pairsTele (b :: rest)))) (pairsTele fresh)).comp
        (swapTeles Ω₂ (pairsTele atoms) (pairsTele fresh))).comp
        (upTele ((upTele s₁ (pairsTele fresh)).comp
          (swapTeles (extendCtx Γ (pairsTele (b :: rest))) [Xh] (pairsTele fresh))) (pairsTele atoms))) =
        (upTele (swapTeles Θ (unpackTele atoms) (pairsTele (a :: b :: rest))) (pairsTele fresh)).comp
          (swapTeles (extendCtx Θ (pairsTele (a :: b :: rest))) (unpackTele atoms) (pairsTele fresh)) :=
      ((congrArg (fun r => BoundCtx.Renaming.comp ((upTele ((upTele pp (pairsTele (b :: rest))).comp
            (swapTeles (Γ.snoc Xh) (pairsTele atoms) (pairsTele (b :: rest)))) (pairsTele fresh)).comp
            (swapTeles Ω₂ (pairsTele atoms) (pairsTele fresh))) r)
          (upTele_comp (pairsTele atoms) (upTele s₁ (pairsTele fresh))
            (swapTeles (extendCtx Γ (pairsTele (b :: rest))) [Xh] (pairsTele fresh))).symm).trans
        ((congrArg (fun r => BoundCtx.Renaming.comp (upTele ((upTele pp (pairsTele (b :: rest))).comp
              (swapTeles (Γ.snoc Xh) (pairsTele atoms) (pairsTele (b :: rest)))) (pairsTele fresh))
            (BoundCtx.Renaming.comp r (upTele (swapTeles (extendCtx Γ (pairsTele (b :: rest))) [Xh]
              (pairsTele fresh)) (pairsTele atoms)))) nat).trans
          ((congrArg (fun r => BoundCtx.Renaming.comp ((upTele ((upTele pp (pairsTele (b :: rest))).comp
                (swapTeles (Γ.snoc Xh) (pairsTele atoms) (pairsTele (b :: rest)))) (pairsTele fresh)).comp
                (upTele (upTele s₁ (pairsTele atoms)) (pairsTele fresh))) r) e₂.symm).trans
            (congrArg (fun r => BoundCtx.Renaming.comp r
                (swapTeles (extendCtx Γ (pairsTele (b :: rest))) (unpackTele atoms) (pairsTele fresh)))
              ((upTele_comp (pairsTele fresh) _ _).trans
                (congrArg (fun r => upTele r (pairsTele fresh)) e₁.symm))))))
    refine (unpackAt_rename (Φ := Φ) atoms ((upTele s₁ (pairsTele fresh)).comp
        (swapTeles (extendCtx Γ (pairsTele (b :: rest))) [Xh] (pairsTele fresh))) _ _).trans
      ((congrArg (fun i => unpackAt atoms i _) index₂).trans (congrArg (unpackAt atoms
        (0 : Fin (teleSize (teleSize (k + 1 + 1) (pairsTele (b :: rest))) (pairsTele fresh) + 1))) ?_))
    refine ((congrArg (fun t => LetCase.LocallyNameless.Tm.rename (upTele ((upTele s₁ (pairsTele fresh)).comp
          (swapTeles (extendCtx Γ (pairsTele (b :: rest))) [Xh] (pairsTele fresh))) (pairsTele atoms)).toFun
          (LetCase.LocallyNameless.Tm.rename (swapTeles Ω₂ (pairsTele atoms) (pairsTele fresh)).toFun t))
        ((LetCase.LocallyNameless.Tm.rename_comp (upTele (upTele pp (pairsTele (b :: rest))) (pairsTele fresh)).toFun
            (upTele (swapTeles (Γ.snoc Xh) (pairsTele atoms) (pairsTele (b :: rest))) (pairsTele fresh)).toFun
            (next.opened (upTele σ (unpackTele atoms))).1).trans
          (congrArg (fun r : BoundCtx.Renaming _ _ => LetCase.LocallyNameless.Tm.rename r.toFun
              (next.opened (upTele σ (unpackTele atoms))).1)
            (upTele_comp (pairsTele fresh) (upTele pp (pairsTele (b :: rest)))
              (swapTeles (Γ.snoc Xh) (pairsTele atoms) (pairsTele (b :: rest))))))).trans ?_).trans
      (CaseTree.renamed_body_term (next.opened (upTele σ (unpackTele atoms))).2 _).symm
    exact (rename_three (next.opened (upTele σ (unpackTele atoms))).1 _ _ _).trans
      (congrArg (fun r : BoundCtx.Renaming _ _ => LetCase.LocallyNameless.Tm.rename r.toFun
        (next.opened (upTele σ (unpackTele atoms))).1) total)

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
  | _, _, _, _, .hold a b rest delay, _, _, _, δ, ρ, π => by
    have h := delay.opened_renamed (ρ.up (tupleTy (a :: b :: rest))) (π.up (tupleTy (a :: b :: rest)))
    rw [renaming_up_comp] at h
    exact congrArg (fun q : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tuple (b :: rest))
        (((δ.snoc (tupleTy (a :: b :: rest))).snoc (.base a)).snoc (tupleTy (b :: rest))) L u =>
      (⟨_, CaseTree.pair a b rest q.2⟩ :
        (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tuple (a :: b :: rest)) (δ.snoc (tupleTy (a :: b :: rest))) L u))
      ((CaseTree.packed_renamed (b :: rest) (delay.opened (ρ.up (tupleTy (a :: b :: rest)))).2
          ((π.up (tupleTy (a :: b :: rest))).up (.base a))).trans
        (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body
            (extendCtx (δ.snoc (tupleTy (a :: b :: rest))) (pairsTele (a :: b :: rest))) L u =>
          (⟨_, CaseTree.packed (b :: rest) r.2⟩ :
            (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tuple (b :: rest))
              (((δ.snoc (tupleTy (a :: b :: rest))).snoc (.base a)).snoc (tupleTy (b :: rest))) L u)) h))

/-- The body of the normal form of a pending tuple commutes with renaming. -/
theorem SpelledTuple.opened_renamed : {n : Nat} → {β : BoundCtx (Ty α) n} → {atoms : List α} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → (d : SpelledTuple atoms β L t) → {m : Nat} →
    {γ : BoundCtx (Ty α) m} → {k : Nat} → {δ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming β γ) →
    (π : BoundCtx.Renaming γ δ) →
    CaseTree.renamed (pending := .body) (d.opened ρ).2 (upTele π (unpackTele atoms)) = d.opened (ρ.comp π)
  | _, _, _, _, .unit body, _, _, _, _, ρ, π => by
    have h := body.normal_renamed (ρ.up _) (π.up _)
    rw [renaming_up_comp] at h
    exact h
  | _, _, _, _, .atom _ body, _, _, _, _, ρ, π => by
    have h := body.normal_renamed (ρ.up _) (π.up _)
    rw [renaming_up_comp] at h
    exact h
  | _, _, _, _, .pair _ _ _ later, _, _, _, _, ρ, π => by
    have h := later.opened_renamed ((ρ.up _).up _) ((π.up _).up _)
    rw [renaming_up_comp, renaming_up_comp] at h
    exact h
  | _, _, _, _, .hold _ _ _ delay, _, _, _, _, ρ, π => by
    have h := delay.opened_renamed (ρ.up _) (π.up _)
    rw [renaming_up_comp] at h
    exact h

/-- The body of the normal form of a chain with a held tuple commutes with
renaming. -/
theorem SpelledDelay.opened_renamed : {a b : α} → {rest : List α} → {n : Nat} → {Δ : BoundCtx (Ty α) n} →
    {s : Slot Δ (tupleTy (a :: b :: rest))} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    (d : SpelledDelay a b rest Δ s L t) → {m : Nat} → {Θ : BoundCtx (Ty α) m} → {k : Nat} →
    {δ : BoundCtx (Ty α) k} → (σ : BoundCtx.Renaming Δ Θ) → (π : BoundCtx.Renaming Θ δ) →
    CaseTree.renamed (pending := .body) (d.opened σ).2 (upTele π (pairsTele (a :: b :: rest))) =
      d.opened (σ.comp π)
  | a, _, _, _, _, _, _, .unpack later, _, _, _, _, σ, π => by
    have h := later.opened_renamed (σ.up (.base a)) (π.up (.base a))
    rw [renaming_up_comp] at h
    exact h
  | a, b, rest, _, _, _, _, .ask g argument reply, _, Θ, _, δ, σ, π => by
    have h := reply.opened_renamed σ π
    have e : (σ.comp (weakenTele Θ (pairsTele (a :: b :: rest)))).comp
        (upTele π (pairsTele (a :: b :: rest))) =
        (σ.comp π).comp (weakenTele δ (pairsTele (a :: b :: rest))) :=
      congrArg (fun r => σ.comp r) (weakenTele_natural (pairsTele (a :: b :: rest)) π)
    simp only [SpelledDelay.opened, CaseTree.renamed]
    rw [assembly_rename_comp, e, h]

/-- The normal form of the bound reply of a request of the chain commutes
with renaming. -/
theorem SpelledDelayTags.opened_renamed : {a b : α} → {rest : List α} → {tags : List (List α)} → {n : Nat} →
    {Δ : BoundCtx (Ty α) n} → {s : Slot Δ (tupleTy (a :: b :: rest))} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → (d : SpelledDelayTags a b rest tags Δ s L t) → {m : Nat} →
    {Θ : BoundCtx (Ty α) m} → {k : Nat} → {δ : BoundCtx (Ty α) k} →
    (σ : BoundCtx.Renaming Δ Θ) → (π : BoundCtx.Renaming Θ δ) →
    CaseTree.renamed (pending := .tags tags)
      (β := (extendCtx Θ (pairsTele (a :: b :: rest))).snoc (tagsTy tags))
      (d.opened σ).2 (upTele π (pairsTele (a :: b :: rest))) = d.opened (σ.comp π)
  | a, b, rest, _, _, _, _, _, .only atoms next, _, Θ, _, δ, σ, π => by
    have ih := next.opened_renamed (upTele σ (unpackTele atoms)) (upTele π (unpackTele atoms))
    rw [upTele_comp] at ih
    have step : CaseTree.renamed (pending := .body)
        (CaseTree.renamed (pending := .body) (next.opened (upTele σ (unpackTele atoms))).2
          (swapTeles Θ (unpackTele atoms) (pairsTele (a :: b :: rest)))).2
        (upTele (upTele π (pairsTele (a :: b :: rest))) (unpackTele atoms)) =
        CaseTree.renamed (pending := .body) (next.opened (upTele (σ.comp π) (unpackTele atoms))).2
          (swapTeles δ (unpackTele atoms) (pairsTele (a :: b :: rest))) :=
      (CaseTree.renamed_body_comp (next.opened (upTele σ (unpackTele atoms))).2
          (swapTeles Θ (unpackTele atoms) (pairsTele (a :: b :: rest)))
          (upTele (upTele π (pairsTele (a :: b :: rest))) (unpackTele atoms))).trans
        ((congrArg (fun r => CaseTree.renamed (pending := .body)
            (next.opened (upTele σ (unpackTele atoms))).2 r)
          (swapTeles_natural (pairsTele (a :: b :: rest)) (unpackTele atoms) π)).trans
          ((CaseTree.renamed_body_comp (next.opened (upTele σ (unpackTele atoms))).2
              (upTele (upTele π (unpackTele atoms)) (pairsTele (a :: b :: rest)))
              (swapTeles δ (unpackTele atoms) (pairsTele (a :: b :: rest)))).symm.trans
            (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body _ L u =>
              CaseTree.renamed (pending := .body) r.2
                (swapTeles δ (unpackTele atoms) (pairsTele (a :: b :: rest)))) ih)))
    simp only [SpelledDelayTags.opened, CaseTree.renamed]
    rw [CaseTree.packed_renamed, step]
  | a, b, rest, _, _, _, _, _, .split atoms nxt more left right, _, Θ, _, δ, σ, π => by
    let Rt : Ty α := tagsTy (atoms :: nxt :: more)
    have ihl := (left.opened_renamed (upTele σ (Rt :: unpackTele atoms))
      (upTele π (Rt :: unpackTele atoms))).trans
      (congrArg (fun r => left.opened r) (upTele_comp (Rt :: unpackTele atoms) σ π))
    have stepl : CaseTree.renamed (pending := .body)
        (CaseTree.renamed (pending := .body) (left.opened (upTele σ (Rt :: unpackTele atoms))).2
          (swapTeles Θ (Rt :: unpackTele atoms) (pairsTele (a :: b :: rest)))).2
        (upTele (upTele π (pairsTele (a :: b :: rest))) (Rt :: unpackTele atoms)) =
        CaseTree.renamed (pending := .body) (left.opened (upTele (σ.comp π) (Rt :: unpackTele atoms))).2
          (swapTeles δ (Rt :: unpackTele atoms) (pairsTele (a :: b :: rest))) :=
      (CaseTree.renamed_body_comp (left.opened (upTele σ (Rt :: unpackTele atoms))).2
          (swapTeles Θ (Rt :: unpackTele atoms) (pairsTele (a :: b :: rest)))
          (upTele (upTele π (pairsTele (a :: b :: rest))) (Rt :: unpackTele atoms))).trans
        ((congrArg (fun r => CaseTree.renamed (pending := .body)
            (left.opened (upTele σ (Rt :: unpackTele atoms))).2 r)
          (swapTeles_natural (pairsTele (a :: b :: rest)) (Rt :: unpackTele atoms) π)).trans
          ((CaseTree.renamed_body_comp (left.opened (upTele σ (Rt :: unpackTele atoms))).2
              (upTele (upTele π (Rt :: unpackTele atoms)) (pairsTele (a :: b :: rest)))
              (swapTeles δ (Rt :: unpackTele atoms) (pairsTele (a :: b :: rest)))).symm.trans
            (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body _ L u =>
              CaseTree.renamed (pending := .body) r.2
                (swapTeles δ (Rt :: unpackTele atoms) (pairsTele (a :: b :: rest)))) ihl)))
    have ihr := (right.opened_renamed (σ.up Rt) (π.up Rt)).trans
      (congrArg (fun r => right.opened r) (renaming_up_comp σ π Rt))
    have comp₁ : CaseTree.renamed (pending := .tags (nxt :: more))
        (β := ((extendCtx Θ (pairsTele (a :: b :: rest))).snoc Rt).snoc (tagsTy (nxt :: more)))
        (CaseTree.renamed (pending := .tags (nxt :: more))
          (β := (extendCtx (Θ.snoc Rt) (pairsTele (a :: b :: rest))).snoc (tagsTy (nxt :: more)))
          (right.opened (σ.up Rt)).2 (swapTeles Θ [Rt] (pairsTele (a :: b :: rest)))).2
        ((upTele π (pairsTele (a :: b :: rest))).up Rt) =
        CaseTree.renamed (pending := .tags (nxt :: more))
          (β := (extendCtx (Θ.snoc Rt) (pairsTele (a :: b :: rest))).snoc (tagsTy (nxt :: more)))
          (right.opened (σ.up Rt)).2
          ((swapTeles Θ [Rt] (pairsTele (a :: b :: rest))).comp ((upTele π (pairsTele (a :: b :: rest))).up Rt)) :=
      CaseTree.renamed_comp (right.opened (σ.up Rt)).2 _ _
    have comp₂ : CaseTree.renamed (pending := .tags (nxt :: more))
        (β := (extendCtx (δ.snoc Rt) (pairsTele (a :: b :: rest))).snoc (tagsTy (nxt :: more)))
        (CaseTree.renamed (pending := .tags (nxt :: more))
          (β := (extendCtx (Θ.snoc Rt) (pairsTele (a :: b :: rest))).snoc (tagsTy (nxt :: more)))
          (right.opened (σ.up Rt)).2 (upTele (π.up Rt) (pairsTele (a :: b :: rest)))).2
        (swapTeles δ [Rt] (pairsTele (a :: b :: rest))) =
        CaseTree.renamed (pending := .tags (nxt :: more))
          (β := (extendCtx (Θ.snoc Rt) (pairsTele (a :: b :: rest))).snoc (tagsTy (nxt :: more)))
          (right.opened (σ.up Rt)).2
          ((upTele (π.up Rt) (pairsTele (a :: b :: rest))).comp (swapTeles δ [Rt] (pairsTele (a :: b :: rest)))) :=
      CaseTree.renamed_comp (right.opened (σ.up Rt)).2 _ _
    have stepr : CaseTree.renamed (pending := .tags (nxt :: more))
        (β := ((extendCtx Θ (pairsTele (a :: b :: rest))).snoc Rt).snoc (tagsTy (nxt :: more)))
        (CaseTree.renamed (pending := .tags (nxt :: more))
          (β := (extendCtx (Θ.snoc Rt) (pairsTele (a :: b :: rest))).snoc (tagsTy (nxt :: more)))
          (right.opened (σ.up Rt)).2 (swapTeles Θ [Rt] (pairsTele (a :: b :: rest)))).2
        ((upTele π (pairsTele (a :: b :: rest))).up Rt) =
        CaseTree.renamed (pending := .tags (nxt :: more))
          (β := (extendCtx (δ.snoc Rt) (pairsTele (a :: b :: rest))).snoc (tagsTy (nxt :: more)))
          (right.opened ((σ.comp π).up Rt)).2 (swapTeles δ [Rt] (pairsTele (a :: b :: rest))) :=
      comp₁.trans
        ((congrArg (fun r => CaseTree.renamed (pending := .tags (nxt :: more))
            (β := (extendCtx (Θ.snoc Rt) (pairsTele (a :: b :: rest))).snoc (tagsTy (nxt :: more)))
            (right.opened (σ.up Rt)).2 r)
          (swapTeles_natural (pairsTele (a :: b :: rest)) [Rt] π)).trans
          (comp₂.symm.trans
            (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tags (nxt :: more)) _ L u =>
              CaseTree.renamed (pending := .tags (nxt :: more))
                (β := (extendCtx (δ.snoc Rt) (pairsTele (a :: b :: rest))).snoc (tagsTy (nxt :: more)))
                r.2 (swapTeles δ [Rt] (pairsTele (a :: b :: rest)))) ihr)))
    have armL := (CaseTree.packed_renamed atoms
        (CaseTree.renamed (pending := .body) (left.opened (upTele σ (Rt :: unpackTele atoms))).2
          (swapTeles Θ (Rt :: unpackTele atoms) (pairsTele (a :: b :: rest)))).2
        ((upTele π (pairsTele (a :: b :: rest))).up Rt)).trans
      (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body
          (extendCtx ((extendCtx δ (pairsTele (a :: b :: rest))).snoc Rt) (unpackTele atoms)) L u =>
        (⟨_, CaseTree.packed atoms r.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tuple atoms)
          (((extendCtx δ (pairsTele (a :: b :: rest))).snoc Rt).snoc (tupleTy atoms)) L u)) stepl)
    exact congrArg₂ (fun (x : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tuple atoms)
          (((extendCtx δ (pairsTele (a :: b :: rest))).snoc Rt).snoc (tupleTy atoms)) L u)
        (y : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tags (nxt :: more))
          (((extendCtx δ (pairsTele (a :: b :: rest))).snoc Rt).snoc (tagsTy (nxt :: more))) L u) =>
        (⟨_, CaseTree.split atoms nxt more x.2 y.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) ×
          CaseTree (.tags (atoms :: nxt :: more)) ((extendCtx δ (pairsTele (a :: b :: rest))).snoc Rt) L u))
      armL stepr

  | a, b, rest, _, _, _, _, _, .keep c d more kept, _, Θ, _, δ, σ, π => by
    let X : Ty α := tupleTy (c :: d :: more)
    have ih := (kept.opened_renamed (σ.up X) (π.up X)).trans
      (congrArg (fun r => kept.opened r) (renaming_up_comp σ π X))
    have step : CaseTree.renamed (pending := .body)
        (CaseTree.renamed (pending := .body) (kept.opened (σ.up X)).2
          (upTele (swapTeles Θ [X] (pairsTele (a :: b :: rest))) (pairsTele (c :: d :: more)))).2
        (upTele (upTele π (pairsTele (a :: b :: rest))) (unpackTele (c :: d :: more))) =
        CaseTree.renamed (pending := .body) (kept.opened ((σ.comp π).up X)).2
          (upTele (swapTeles δ [X] (pairsTele (a :: b :: rest))) (pairsTele (c :: d :: more))) :=
      (CaseTree.renamed_body_comp (kept.opened (σ.up X)).2
          (upTele (swapTeles Θ [X] (pairsTele (a :: b :: rest))) (pairsTele (c :: d :: more)))
          (upTele (upTele π (pairsTele (a :: b :: rest))) (unpackTele (c :: d :: more)))).trans
        ((congrArg (fun r => CaseTree.renamed (pending := .body) (kept.opened (σ.up X)).2 r)
          ((upTele_comp (pairsTele (c :: d :: more)) _ _).trans
            ((congrArg (fun r => upTele r (pairsTele (c :: d :: more)))
              (swapTeles_natural (pairsTele (a :: b :: rest)) [X] π)).trans
              (upTele_comp (pairsTele (c :: d :: more)) (upTele (π.up X) (pairsTele (a :: b :: rest)))
                (swapTeles δ [X] (pairsTele (a :: b :: rest)))).symm))).trans
          ((CaseTree.renamed_body_comp (kept.opened (σ.up X)).2
              (upTele (upTele (π.up X) (pairsTele (a :: b :: rest))) (pairsTele (c :: d :: more)))
              (upTele (swapTeles δ [X] (pairsTele (a :: b :: rest))) (pairsTele (c :: d :: more)))).symm.trans
            (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body _ L u =>
              CaseTree.renamed (pending := .body) r.2
                (upTele (swapTeles δ [X] (pairsTele (a :: b :: rest))) (pairsTele (c :: d :: more)))) ih)))
    exact congrArg (fun q : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tuple (c :: d :: more))
          ((extendCtx δ (pairsTele (a :: b :: rest))).snoc X) L u =>
        (⟨_, CaseTree.only (c :: d :: more) q.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) ×
          CaseTree (.tags [c :: d :: more]) ((extendCtx δ (pairsTele (a :: b :: rest))).snoc X) L u))
      ((CaseTree.packed_renamed (c :: d :: more)
          (CaseTree.renamed (pending := .body) (kept.opened (σ.up X)).2
            (upTele (swapTeles Θ [X] (pairsTele (a :: b :: rest))) (pairsTele (c :: d :: more)))).2
          (upTele π (pairsTele (a :: b :: rest)))).trans
        (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body
            (extendCtx (extendCtx δ (pairsTele (a :: b :: rest))) (unpackTele (c :: d :: more))) L u =>
          (⟨_, CaseTree.packed (c :: d :: more) r.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) ×
            CaseTree (.tuple (c :: d :: more)) ((extendCtx δ (pairsTele (a :: b :: rest))).snoc X) L u)) step))

/-- The body of the normal form of a subchain with a fresh tuple kept
packed commutes with renaming. -/
theorem SpelledKept.opened_renamed : {a b : α} → {rest fresh : List α} → {n : Nat} →
    {Δ : BoundCtx (Ty α) n} → {s : Slot Δ (tupleTy (a :: b :: rest))} → {x : Slot Δ (tupleTy fresh)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → (d : SpelledKept a b rest fresh Δ s x L t) → {m : Nat} →
    {Θ : BoundCtx (Ty α) m} → {k : Nat} → {δ : BoundCtx (Ty α) k} → (σ : BoundCtx.Renaming Δ Θ) →
    (π : BoundCtx.Renaming Θ δ) →
    CaseTree.renamed (pending := .body) (d.opened σ).2
      (upTele (upTele π (pairsTele (a :: b :: rest))) (pairsTele fresh)) = d.opened (σ.comp π)
  | a, b, rest, fresh, _, _, _, _, _, .release next, _, Θ, _, δ, σ, π => by
    have ih := (next.opened_renamed (upTele σ (pairsTele fresh)) (upTele π (pairsTele fresh))).trans
      (congrArg (fun r => next.opened r) (upTele_comp (pairsTele fresh) σ π))
    exact (CaseTree.renamed_body_comp (next.opened (upTele σ (pairsTele fresh))).2
        (swapTeles Θ (pairsTele fresh) (pairsTele (a :: b :: rest)))
        (upTele (upTele π (pairsTele (a :: b :: rest))) (pairsTele fresh))).trans
      ((congrArg (fun r => CaseTree.renamed (pending := .body)
          (next.opened (upTele σ (pairsTele fresh))).2 r)
        (swapTeles_natural (pairsTele (a :: b :: rest)) (pairsTele fresh) π)).trans
        ((CaseTree.renamed_body_comp (next.opened (upTele σ (pairsTele fresh))).2
            (upTele (upTele π (pairsTele fresh)) (pairsTele (a :: b :: rest)))
            (swapTeles δ (pairsTele fresh) (pairsTele (a :: b :: rest)))).symm.trans
          (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body _ L u =>
            CaseTree.renamed (pending := .body) r.2
              (swapTeles δ (pairsTele fresh) (pairsTele (a :: b :: rest)))) ih)))
  | a, b, rest, fresh, _, _, _, _, _, .ask g argument reply, _, Θ, _, δ, σ, π => by
    have h := reply.opened_renamed σ π
    have e : ((σ.comp (weakenTele Θ (pairsTele (a :: b :: rest)))).comp
        (weakenTele (extendCtx Θ (pairsTele (a :: b :: rest))) (pairsTele fresh))).comp
        (upTele (upTele π (pairsTele (a :: b :: rest))) (pairsTele fresh)) =
        ((σ.comp π).comp (weakenTele δ (pairsTele (a :: b :: rest)))).comp
          (weakenTele (extendCtx δ (pairsTele (a :: b :: rest))) (pairsTele fresh)) :=
      (congrArg (fun r => BoundCtx.Renaming.comp (σ.comp (weakenTele Θ (pairsTele (a :: b :: rest)))) r)
        (weakenTele_natural (pairsTele fresh) (upTele π (pairsTele (a :: b :: rest))))).trans
        (congrArg (fun r => BoundCtx.Renaming.comp (σ.comp r)
            (weakenTele (extendCtx δ (pairsTele (a :: b :: rest))) (pairsTele fresh)))
          (weakenTele_natural (pairsTele (a :: b :: rest)) π))
    simp only [SpelledKept.opened, CaseTree.renamed]
    rw [assembly_rename_comp, e, h]

/-- The normal form of the bound reply of a request of such a subchain
commutes with renaming. -/
theorem SpelledKeptTags.opened_renamed : {a b : α} → {rest fresh : List α} → {tags : List (List α)} →
    {n : Nat} → {Δ : BoundCtx (Ty α) n} → {s : Slot Δ (tupleTy (a :: b :: rest))} →
    {x : Slot Δ (tupleTy fresh)} → {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} →
    (d : SpelledKeptTags a b rest fresh tags Δ s x L t) → {m : Nat} → {Θ : BoundCtx (Ty α) m} →
    {k : Nat} → {δ : BoundCtx (Ty α) k} → (σ : BoundCtx.Renaming Δ Θ) → (π : BoundCtx.Renaming Θ δ) →
    CaseTree.renamed (pending := .tags tags)
      (β := (extendCtx (extendCtx Θ (pairsTele (a :: b :: rest))) (pairsTele fresh)).snoc (tagsTy tags))
      (d.opened σ).2 (upTele (upTele π (pairsTele (a :: b :: rest))) (pairsTele fresh)) =
      d.opened (σ.comp π)
  | a, b, rest, fresh, _, _, _, _, _, _, .only atoms next, _, Θ, _, δ, σ, π => by
    have ih := (next.opened_renamed (upTele σ (unpackTele atoms)) (upTele π (unpackTele atoms))).trans
      (congrArg (fun r => next.opened r) (upTele_comp (unpackTele atoms) σ π))
    have e : ((upTele (swapTeles Θ (unpackTele atoms) (pairsTele (a :: b :: rest))) (pairsTele fresh)).comp
          (swapTeles (extendCtx Θ (pairsTele (a :: b :: rest))) (unpackTele atoms) (pairsTele fresh))).comp
        (upTele (upTele (upTele π (pairsTele (a :: b :: rest))) (pairsTele fresh)) (unpackTele atoms)) =
        (upTele (upTele (upTele π (unpackTele atoms)) (pairsTele (a :: b :: rest))) (pairsTele fresh)).comp
          ((upTele (swapTeles δ (unpackTele atoms) (pairsTele (a :: b :: rest))) (pairsTele fresh)).comp
            (swapTeles (extendCtx δ (pairsTele (a :: b :: rest))) (unpackTele atoms) (pairsTele fresh))) :=
      (congrArg (fun r => BoundCtx.Renaming.comp
          (upTele (swapTeles Θ (unpackTele atoms) (pairsTele (a :: b :: rest))) (pairsTele fresh)) r)
        (swapTeles_natural (pairsTele fresh) (unpackTele atoms) (upTele π (pairsTele (a :: b :: rest))))).trans
        (congrArg (fun r => BoundCtx.Renaming.comp r
            (swapTeles (extendCtx δ (pairsTele (a :: b :: rest))) (unpackTele atoms) (pairsTele fresh)))
          ((upTele_comp (pairsTele fresh) _ _).trans
            ((congrArg (fun r => upTele r (pairsTele fresh))
              (swapTeles_natural (pairsTele (a :: b :: rest)) (unpackTele atoms) π)).trans
              (upTele_comp (pairsTele fresh) (upTele (upTele π (unpackTele atoms)) (pairsTele (a :: b :: rest)))
                (swapTeles δ (unpackTele atoms) (pairsTele (a :: b :: rest)))).symm)))
    have step : CaseTree.renamed (pending := .body)
        (CaseTree.renamed (pending := .body) (next.opened (upTele σ (unpackTele atoms))).2
          ((upTele (swapTeles Θ (unpackTele atoms) (pairsTele (a :: b :: rest))) (pairsTele fresh)).comp
            (swapTeles (extendCtx Θ (pairsTele (a :: b :: rest))) (unpackTele atoms) (pairsTele fresh)))).2
        (upTele (upTele (upTele π (pairsTele (a :: b :: rest))) (pairsTele fresh)) (unpackTele atoms)) =
        CaseTree.renamed (pending := .body) (next.opened (upTele (σ.comp π) (unpackTele atoms))).2
          ((upTele (swapTeles δ (unpackTele atoms) (pairsTele (a :: b :: rest))) (pairsTele fresh)).comp
            (swapTeles (extendCtx δ (pairsTele (a :: b :: rest))) (unpackTele atoms) (pairsTele fresh))) :=
      (CaseTree.renamed_body_comp (next.opened (upTele σ (unpackTele atoms))).2
          ((upTele (swapTeles Θ (unpackTele atoms) (pairsTele (a :: b :: rest))) (pairsTele fresh)).comp
            (swapTeles (extendCtx Θ (pairsTele (a :: b :: rest))) (unpackTele atoms) (pairsTele fresh)))
          (upTele (upTele (upTele π (pairsTele (a :: b :: rest))) (pairsTele fresh)) (unpackTele atoms))).trans
        ((congrArg (fun r => CaseTree.renamed (pending := .body)
            (next.opened (upTele σ (unpackTele atoms))).2 r) e).trans
          ((CaseTree.renamed_body_comp (next.opened (upTele σ (unpackTele atoms))).2
              (upTele (upTele (upTele π (unpackTele atoms)) (pairsTele (a :: b :: rest))) (pairsTele fresh))
              ((upTele (swapTeles δ (unpackTele atoms) (pairsTele (a :: b :: rest))) (pairsTele fresh)).comp
                (swapTeles (extendCtx δ (pairsTele (a :: b :: rest))) (unpackTele atoms)
                  (pairsTele fresh)))).symm.trans
            (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body _ L u =>
              CaseTree.renamed (pending := .body) r.2
                ((upTele (swapTeles δ (unpackTele atoms) (pairsTele (a :: b :: rest))) (pairsTele fresh)).comp
                  (swapTeles (extendCtx δ (pairsTele (a :: b :: rest))) (unpackTele atoms)
                    (pairsTele fresh)))) ih)))
    exact congrArg (fun q : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tuple atoms)
          ((extendCtx (extendCtx δ (pairsTele (a :: b :: rest))) (pairsTele fresh)).snoc (tupleTy atoms)) L u =>
        (⟨_, CaseTree.only atoms q.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tags [atoms])
          ((extendCtx (extendCtx δ (pairsTele (a :: b :: rest))) (pairsTele fresh)).snoc (tupleTy atoms)) L u))
      ((CaseTree.packed_renamed atoms
          (CaseTree.renamed (pending := .body) (next.opened (upTele σ (unpackTele atoms))).2
            ((upTele (swapTeles Θ (unpackTele atoms) (pairsTele (a :: b :: rest))) (pairsTele fresh)).comp
              (swapTeles (extendCtx Θ (pairsTele (a :: b :: rest))) (unpackTele atoms) (pairsTele fresh)))).2
          (upTele (upTele π (pairsTele (a :: b :: rest))) (pairsTele fresh))).trans
        (congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body
            (extendCtx (extendCtx (extendCtx δ (pairsTele (a :: b :: rest))) (pairsTele fresh))
              (unpackTele atoms)) L u =>
          (⟨_, CaseTree.packed atoms r.2⟩ : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree (.tuple atoms)
            ((extendCtx (extendCtx δ (pairsTele (a :: b :: rest))) (pairsTele fresh)).snoc (tupleTy atoms))
              L u)) step))

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
