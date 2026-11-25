module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Wiring.Evaluation.Thms
public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Wiring.JumpResolution.Thms

public section

universe u v w

namespace Silmaril.Calco2019.Proofs.IterationJumpEvaluation

open CategoryTheory CategoryTheory.Limits Guardedness IterationTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K}
  (F : (greatest P).Conway)

local notation "solve" => fun f => F.iterate f True.intro

private theorem stages {A B Y : K} (a : A ⟶ P.sum (P.sum Y A) B)
    (b : B ⟶ P.sum (P.sum Y A) B) :
    let v := solve b
    let u := solve (a ≫ P.desc (𝟙 _) v)
    solve (P.desc a b ≫ P.assoc) = P.desc u (v ≫ P.desc (𝟙 Y) u) := by
  dsimp
  let D : TwoStateBody (greatest P) (P.sum A B) Y A B :=
    ⟨P.map P.inr (𝟙 B), a, b, trivial⟩
  have entry : (P.map (P.inr (X := Y) (Y := A)) (𝟙 B)) ≫ P.assoc = P.inr := by
    apply P.hom_ext <;> simp [Coproducts.map, Coproducts.assoc]
  have h := D.feedback_vanish_pair F
  change P.map P.inr (𝟙 B) ≫ P.assoc ≫ P.desc (𝟙 Y)
        (solve (P.desc a b ≫ P.assoc)) =
      P.map P.inr (𝟙 B) ≫ P.desc (𝟙 (P.sum Y A)) (solve b) ≫
        P.desc (𝟙 Y) (solve (a ≫ P.desc (𝟙 (P.sum Y A)) (solve b))) at h
  rw [← Category.assoc (P.map P.inr (𝟙 B)) P.assoc, entry] at h
  simpa using h

private theorem nonrecursive {A Y : K} (f : A ⟶ Y) :
    solve (f ≫ P.inl) = f := by
  have h := F.fixpoint (f ≫ P.inl) True.intro
  change (f ≫ P.inl) ≫ P.desc (𝟙 Y) (solve (f ≫ P.inl)) = solve (f ≫ P.inl) at h
  simpa using h.symm

private theorem bottom_natural {A B D : K} (f : B ⟶ D) :
    solve (P.inr (X := B) (Y := A)) ≫ f = solve (P.inr (X := D) (Y := A)) := by
  have h := F.naturalCodiagonal.naturality (P.inr (X := B) (Y := A)) f True.intro True.intro
  have edge : P.inr ≫ P.map f (𝟙 A) = P.inr := by simp [Coproducts.map]
  rw [edge] at h
  exact h.symm

private theorem map_comp {A B D Y : K} (f : A ⟶ B) (g : B ⟶ D) :
    P.map (𝟙 Y) f ≫ P.map (𝟙 Y) g = P.map (𝟙 Y) (f ≫ g) := by
  apply P.hom_ext <;> simp [Coproducts.map]

private theorem assocInv_assoc {A B D : K} :
    P.assocInv (X := A) (Y := B) (Z := D) ≫ P.assoc = 𝟙 _ := by
  apply P.hom_ext
  · simp [Coproducts.assocInv, Coproducts.assoc]
  · apply P.hom_ext <;> simp [Coproducts.assocInv, Coproducts.assoc, Coproducts.map]

variable {X : K} (C : FiniteCopowers X) {σ : Signature.{w}} {I E : Arity}
  (op : ∀ a : σ.Symbol, X ⟶ (C.cofan (Fin (σ.arity a))).pt)
  (g : Wiring σ I E) (s : g.states)

private noncomputable def splitState :
    (C.cofan g.states).pt ⟶ P.sum (C.cofan (g.without s)).pt X :=
  open Classical in
  Cofan.IsColimit.desc (C.colimit g.states) fun r =>
    if h : r = s then P.inr else (C.cofan (g.without s)).inj ⟨r, h⟩ ≫ P.inl

private theorem splitState_selected :
    (C.cofan g.states).inj s ≫ splitState (P := P) C g s = P.inr := by
  unfold splitState
  rw [Cofan.IsColimit.fac]
  simp

private theorem splitState_other (t : g.without s) :
    (C.cofan g.states).inj t.val ≫ splitState (P := P) C g s =
      (C.cofan (g.without s)).inj t ≫ P.inl := by
  unfold splitState
  rw [Cofan.IsColimit.fac]
  simp [t.property]

private theorem splitState_remaining :
    C.reindex (Subtype.val : g.without s → g.states) ≫ splitState (P := P) C g s = P.inl := by
  apply Cofan.IsColimit.hom_ext (C.colimit (g.without s))
  intro t
  rw [C.reindex_inj_assoc, splitState_other]

private noncomputable def stateIso :
    (C.cofan g.states).pt ≅ P.sum (C.cofan (g.without s)).pt X where
  hom := splitState C g s
  inv := P.desc (C.reindex (Subtype.val : g.without s → g.states)) ((C.cofan g.states).inj s)
  hom_inv_id := by
    apply Cofan.IsColimit.hom_ext (C.colimit g.states)
    intro r
    by_cases h : r = s
    · subst r
      rw [← Category.assoc, splitState_selected, P.inr_desc, Category.comp_id]
    · rw [← Category.assoc, splitState_other C g s ⟨r, h⟩,
        Category.assoc, P.inl_desc, C.reindex_inj, Category.comp_id]
  inv_hom_id := by
    apply P.hom_ext
    · rw [P.inl_desc_assoc, splitState_remaining, Category.comp_id]
    · rw [P.inr_desc_assoc, splitState_selected, Category.comp_id]

private noncomputable def flattened :
    (C.cofan g.states).pt ⟶ P.sum (P.sum (C.cofan E).pt (C.cofan (g.without s)).pt) X :=
  g.body C F.toFixpoints op ≫ P.map (𝟙 (C.cofan E).pt) (splitState C g s) ≫ P.assocInv

private noncomputable def left :
    (C.cofan (g.without s)).pt ⟶ P.sum (P.sum (C.cofan E).pt (C.cofan (g.without s)).pt) X :=
  C.reindex (Subtype.val : g.without s → g.states) ≫ flattened F C op g s

private noncomputable def right :
    X ⟶ P.sum (P.sum (C.cofan E).pt (C.cofan (g.without s)).pt) X :=
  (C.cofan g.states).inj s ≫ flattened F C op g s

private theorem solution_split :
    let v := solve (right F C op g s)
    let u := solve (left F C op g s ≫ P.desc (𝟙 _) v)
    solve (g.body C F.toFixpoints op) =
      splitState C g s ≫ P.desc u (v ≫ P.desc (𝟙 (C.cofan E).pt) u) := by
  let i := stateIso (P := P) C g s
  have branches : P.desc (left F C op g s) (right F C op g s) =
      i.inv ≫ flattened F C op g s := by
    simp [left, right, i, stateIso]
  have square : i.hom ≫ (P.desc (left F C op g s) (right F C op g s) ≫ P.assoc) =
      g.body C F.toFixpoints op ≫ P.map (𝟙 (C.cofan E).pt) i.hom := by
    simp only [branches, Category.assoc, i.hom_inv_id_assoc]
    simp [flattened, i, stateIso, assocInv_assoc]
  dsimp
  exact (F.uniform_iso i _ _ True.intro True.intro square).symm.trans
    (congrArg (fun k => i.hom ≫ k) (stages F _ _))

private theorem right_row :
    right F C op g s =
      Wiring.branch C F.toFixpoints op (g.row s) ≫
        P.map (𝟙 (C.cofan E).pt) (splitState C g s) ≫ P.assocInv := by
  have row : (C.cofan g.states).inj s ≫ g.body C F.toFixpoints op =
      Wiring.branch C F.toFixpoints op (g.row s) :=
    Cofan.IsColimit.fac (C.colimit g.states) _ s
  unfold right flattened
  rw [← Category.assoc, row]

private theorem left_row (t : g.without s) :
    (C.cofan (g.without s)).inj t ≫ left F C op g s =
      Wiring.branch C F.toFixpoints op (g.row t.val) ≫
        P.map (𝟙 (C.cofan E).pt) (splitState C g s) ≫ P.assocInv := by
  have row : (C.cofan g.states).inj t.val ≫ g.body C F.toFixpoints op =
      Wiring.branch C F.toFixpoints op (g.row t.val) :=
    Cofan.IsColimit.fac (C.colimit g.states) _ t.val
  unfold left flattened
  rw [C.reindex_inj_assoc, ← Category.assoc, row]

theorem evaluate_cut (row : g.row s = .jump s) :
    (g.cut s).evaluate C F.toFixpoints op = g.evaluate C F.toFixpoints op := by
  classical
  let Y := (C.cofan E).pt
  let A := (C.cofan (g.without s)).pt
  let k := P.inr (X := P.sum Y A) (Y := X)
  let constant := solve (P.inr (X := Y) (Y := X)) ≫ P.inl (X := Y) (Y := A)
  have original : right F C op g s = k := by
    rw [right_row, row]
    change ((C.cofan g.states).inj s ≫ P.inr) ≫ P.map (𝟙 Y) (splitState C g s) ≫ P.assocInv = k
    simp only [Category.assoc, Coproducts.map, P.inr_desc_assoc]
    rw [← Category.assoc ((C.cofan g.states).inj s), splitState_selected]
    simp [Coproducts.assocInv, Coproducts.map, k]
  have replaced : right F C op (g.cut s) s = constant ≫ P.inl := by
    rw [right_row]
    change Wiring.branch C F.toFixpoints op (if s = s then .head .bottom else g.row s) ≫
      P.map (𝟙 Y) (splitState C g s) ≫ P.assocInv = constant ≫ P.inl
    simp [Wiring.branch, Wiring.interpretation, Interpretation.branch, constant,
      Coproducts.map, Coproducts.assocInv, Y]
  have v : solve (right F C op (g.cut s) s) = solve (right F C op g s) := by
    let iter : (X ⟶ P.sum (P.sum Y A) X) → (X ⟶ P.sum Y A) := solve
    exact (congrArg iter replaced).trans ((nonrecursive F constant).trans
      ((bottom_natural F (P.inl (X := Y) (Y := A))).trans (congrArg iter original).symm))
  have a : left F C op (g.cut s) s = left F C op g s := by
    apply Cofan.IsColimit.hom_ext (C.colimit (g.without s))
    intro t
    rw [left_row F C op (g.cut s) s t, left_row F C op g s t]
    change Wiring.branch C F.toFixpoints op (if t.val = s then .head .bottom else g.row t.val) ≫
      P.map (𝟙 Y) (splitState C g s) ≫ P.assocInv = _
    rw [ite_eq_right t.property]
  let combined (a : A ⟶ P.sum (P.sum Y A) X) (b : X ⟶ P.sum Y A) :
      P.sum A X ⟶ Y :=
    let u := solve (a ≫ P.desc (𝟙 _) b)
    P.desc u (b ≫ P.desc (𝟙 Y) u)
  have same : solve ((g.cut s).body C F.toFixpoints op) = solve (g.body C F.toFixpoints op) := by
    calc
      _ = splitState C g s ≫ combined (left F C op (g.cut s) s) (solve (right F C op (g.cut s) s)) :=
        solution_split F C op (g.cut s) s
      _ = splitState C g s ≫ combined (left F C op g s) (solve (right F C op g s)) := by
        rw [a, v]
      _ = _ := (solution_split F C op g s).symm
  exact congrArg (fun j => C.reindex g.entry ≫ j) same

private theorem split_redirect (t : g.without s) :
    splitState (P := P) C g s ≫ P.desc (𝟙 _) ((C.cofan (g.without s)).inj t) =
      C.reindex (g.redirect s t) := by
  classical
  apply Cofan.IsColimit.hom_ext (C.colimit g.states)
  intro r
  rw [C.reindex_inj, ← Category.assoc]
  by_cases h : r = s
  · subst r
    rw [splitState_selected, P.inr_desc]
    simp [Wiring.redirect]
  · rw [splitState_other C g s ⟨r, h⟩, Category.assoc, P.inl_desc, Category.comp_id]
    simp [Wiring.redirect, h]

private theorem contract_branch (t r : g.without s) :
    Wiring.branch C F.toFixpoints op ((g.contract s t).row r) =
      Wiring.branch C F.toFixpoints op (g.row r.val) ≫
        P.map (𝟙 (C.cofan E).pt) (C.reindex (g.redirect s t)) := by
  change Wiring.branch C F.toFixpoints op
      ((g.row r.val).connect (g.redirect s t) (fun e => .head (.exit e))) = _
  cases g.row r.val with
  | jump j =>
    simp [Instruction.connect, Wiring.branch, Coproducts.map]
  | head h =>
    have rename :
        (Instruction.head h).connect (g.redirect s t) (fun e => .head (.exit e)) =
          .head (h.mapState (g.redirect s t)) := by
      cases h <;> rfl
    rw [rename]
    exact ((Wiring.interpretation C F.toFixpoints op).branch_reindex (g.redirect s t) h).symm

theorem evaluate_contract (t : g.without s) (row : g.row s = .jump t.val) :
    (g.contract s t).evaluate C F.toFixpoints op = g.evaluate C F.toFixpoints op := by
  let Y := (C.cofan E).pt
  let A := (C.cofan (g.without s)).pt
  let target := (C.cofan (g.without s)).inj t
  let retain := P.desc (𝟙 A) target
  let redirect := C.reindex (g.redirect s t)
  have b : right F C op g s = (target ≫ P.inr) ≫ P.inl := by
    rw [right_row, row]
    change ((C.cofan g.states).inj t.val ≫ P.inr) ≫
      P.map (𝟙 Y) (splitState C g s) ≫ P.assocInv = _
    simp only [Category.assoc, Coproducts.map, P.inr_desc_assoc]
    rw [← Category.assoc ((C.cofan g.states).inj t.val), splitState_other]
    simp [Coproducts.assocInv, Coproducts.map, target]
  have v : solve (right F C op g s) = target ≫ P.inr :=
    (congrArg (fun k : X ⟶ P.sum (P.sum Y A) X => solve k) b).trans (nonrecursive F _)
  have shift : P.assocInv ≫ P.desc (𝟙 (P.sum Y A)) (target ≫ P.inr) =
      P.map (𝟙 Y) retain := by
    apply P.hom_ext
    · simp [Coproducts.assocInv, Coproducts.map]
    · apply P.hom_ext <;> simp [Coproducts.assocInv, Coproducts.map, retain, A, Y]
  have ubody : left F C op g s ≫ P.desc (𝟙 (P.sum Y A)) (solve (right F C op g s)) =
      (g.contract s t).body C F.toFixpoints op := by
    apply Cofan.IsColimit.hom_ext (C.colimit (g.without s))
    intro r
    have rr : (C.cofan (g.without s)).inj r ≫ (g.contract s t).body C F.toFixpoints op =
        Wiring.branch C F.toFixpoints op ((g.contract s t).row r) :=
      Cofan.IsColimit.fac (C.colimit (g.without s)) _ r
    rw [← Category.assoc, left_row, Category.assoc, Category.assoc, v, shift,
      map_comp, split_redirect, rr, contract_branch]
  let u := solve ((g.contract s t).body C F.toFixpoints op)
  have ueq : solve (left F C op g s ≫ P.desc (𝟙 _) (solve (right F C op g s))) = u :=
    congrArg (fun k : A ⟶ P.sum Y A => solve k) ubody
  have assemble : P.desc u ((target ≫ P.inr) ≫ P.desc (𝟙 Y) u) = retain ≫ u := by
    simp [retain, A, Y]
  have all : solve (g.body C F.toFixpoints op) = redirect ≫ u := by
    calc
      _ = _ := solution_split F C op g s
      _ = splitState C g s ≫ (retain ≫ u) := by rw [ueq, v, assemble]
      _ = _ := by rw [← Category.assoc, split_redirect]
  change C.reindex (g.redirect s t ∘ g.entry) ≫ u =
    C.reindex g.entry ≫ solve (g.body C F.toFixpoints op)
  rw [← C.reindex_comp]
  exact (Category.assoc _ _ _).trans (congrArg (fun k => C.reindex g.entry ≫ k) all.symm)

theorem normalization_evaluate {r : Wiring.Ranked σ I E} (h : g.Normalizes r) :
    r.toWiring.evaluate C F.toFixpoints op = g.evaluate C F.toFixpoints op := by
  induction h with
  | done _ => rfl
  | cut s row _ ih => exact ih.trans (evaluate_cut F C op _ s row)
  | contract s t row _ ih => exact ih.trans (evaluate_contract F C op _ s t row)

theorem ranked_component (r : Wiring.Ranked σ I E) (i : I) :
    (C.cofan I).inj i ≫ r.toWiring.evaluate C F.toFixpoints op =
      (Wiring.interpretation C F.toFixpoints op).solution F.toFixpoints r.system (r.entry i) := by
  change (C.cofan I).inj i ≫ C.reindex r.entry ≫ solve (r.toWiring.body C F.toFixpoints op) = _
  rw [C.reindex_inj_assoc]
  rfl

end Silmaril.Calco2019.Proofs.IterationJumpEvaluation
