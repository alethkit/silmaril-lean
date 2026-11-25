module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Wiring.Evaluation.Defs

public section

universe u v w

namespace Silmaril.Calco2019.Proofs.IterationWiringEvaluation

open CategoryTheory CategoryTheory.Limits Guardedness IterationTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K}
  (F : (greatest P).Conway)

local notation "solve" => fun f => F.iterate f True.intro

theorem feedback_rewire {S I E : K} (b : S ⟶ P.sum (P.sum E I) S) (entry : I ⟶ S) :
    entry ≫ solve (b ≫ P.desc (P.map (𝟙 E) entry) P.inr) =
      solve (entry ≫ solve b) := by
  let remap := P.map (𝟙 E) entry
  let lift := P.map remap (𝟙 S)
  have join : lift ≫ P.merge = P.desc remap P.inr := by
    simp [lift, Coproducts.merge]
  have first : solve (b ≫ P.desc remap P.inr) = solve (solve b ≫ remap) := by
    rw [← join, ← Category.assoc]
    calc
      _ = solve (solve (b ≫ lift)) := F.naturalCodiagonal.codiagonal _
        (by constructor) True.intro True.intro True.intro
      _ = _ := congrArg (fun k : S ⟶ P.sum E S => solve k)
        (F.naturalCodiagonal.naturality b remap True.intro True.intro)
  let g := solve b
  let h := entry ≫ P.inr (X := E)
  have left : P.desc P.inl h = remap := by simp [h, remap, Coproducts.map]
  have right : h ≫ P.desc P.inl g = entry ≫ g := by simp [h]
  have rolling := F.dinaturality g h (Or.inl True.intro) True.intro True.intro
  rw [left, right] at rolling
  rw [first]
  calc
    _ = entry ≫ (g ≫ P.desc (𝟙 E) (solve (entry ≫ g))) :=
      congrArg (fun k : S ⟶ E => entry ≫ k) rolling
    _ = _ := (Category.assoc _ _ _).symm.trans (F.fixpoint (entry ≫ g) True.intro)

private theorem bottom_natural {A B D : K} (f : B ⟶ D) :
    solve (P.inr (X := B) (Y := A)) ≫ f = solve (P.inr (X := D) (Y := A)) := by
  have h := F.naturalCodiagonal.naturality (P.inr (X := B) (Y := A)) f True.intro True.intro
  have edge : P.inr ≫ P.map f (𝟙 A) = P.inr := by simp [Coproducts.map]
  rw [edge] at h
  exact h.symm

theorem staged_comp {S T J E : K} (a : S ⟶ P.sum J S) (b : T ⟶ P.sum E T)
    (next : J ⟶ T) :
    P.inl ≫ solve
      (P.desc (a ≫ P.desc (next ≫ P.inr) (P.inr ≫ P.inl))
        (b ≫ P.map (P.inl (X := E) (Y := S)) (𝟙 T)) ≫ P.assoc) =
    solve a ≫ next ≫ solve b := by
  let left : S ⟶ P.sum (P.sum E S) T := a ≫ P.desc (next ≫ P.inr) (P.inr ≫ P.inl)
  let right := b ≫ P.map (P.inl (X := E) (Y := S)) (𝟙 T)
  let D : TwoStateBody (greatest P) S E S T :=
    ⟨P.inr ≫ P.inl, left, right, trivial⟩
  have v : solve right = solve b ≫ P.inl :=
    F.naturalCodiagonal.naturality b P.inl True.intro True.intro
  have q : left ≫ P.desc (𝟙 (P.sum E S)) (solve right) =
      a ≫ P.map (next ≫ solve b) (𝟙 S) := by
    dsimp only [left]
    simp [Coproducts.map]
    exact congrArg (fun k : T ⟶ P.sum E S => a ≫ P.desc (next ≫ k) P.inr) v
  have u : solve (left ≫ P.desc (𝟙 (P.sum E S)) (solve right)) =
      solve a ≫ next ≫ solve b :=
    (congrArg (fun k : S ⟶ P.sum E S => solve k) q).trans
      (F.naturalCodiagonal.naturality a (next ≫ solve b) True.intro True.intro)
  have h := D.feedback_vanish_pair F
  change (P.inr ≫ P.inl) ≫ P.assoc ≫ P.desc (𝟙 E)
        (solve (P.desc left right ≫ P.assoc)) =
      (P.inr ≫ P.inl) ≫ P.desc (𝟙 (P.sum E S)) (solve right) ≫
        P.desc (𝟙 E) (solve (left ≫ P.desc (𝟙 (P.sum E S)) (solve right))) at h
  have entry : (P.inr ≫ P.inl : S ⟶ P.sum (P.sum E S) T) ≫ P.assoc = P.inl ≫ P.inr := by
    simp [Coproducts.assoc]
  rw [← Category.assoc (P.inr ≫ P.inl) P.assoc, entry] at h
  simpa only [Category.assoc, P.inr_desc, P.inl_desc_assoc, Category.id_comp, u] using h

variable {X : K} (C : FiniteCopowers X) {σ : Signature.{w}}
  (op : ∀ a : σ.Symbol, X ⟶ (C.cofan (Fin (σ.arity a))).pt) {I E : Arity}

private theorem body_row (g : Wiring σ I E) (s : g.states) :
    (C.cofan g.states).inj s ≫ g.body C F.toFixpoints op = Wiring.branch C F.toFixpoints op (g.row s) :=
  Cofan.IsColimit.fac (C.colimit g.states) _ s

private theorem solution_row (g : Wiring σ I E) (s : g.states) :
    (C.cofan g.states).inj s ≫ solve (g.body C F.toFixpoints op) =
      Wiring.branch C F.toFixpoints op (g.row s) ≫
        P.desc (𝟙 _) (solve (g.body C F.toFixpoints op)) := by
  have fixed := F.fixpoint (g.body C F.toFixpoints op) True.intro
  change g.body C F.toFixpoints op ≫ P.desc (𝟙 _) (solve (g.body C F.toFixpoints op)) =
    solve (g.body C F.toFixpoints op) at fixed
  exact (congrArg (fun k => (C.cofan g.states).inj s ≫ k) fixed).symm.trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ _) (body_row F C op g s)))

theorem evaluate_base (f : I → E) :
    (Wiring.base (σ := σ) f).evaluate C F.toFixpoints op = C.reindex f := by
  apply Cofan.IsColimit.hom_ext (C.colimit I)
  intro i
  change (C.cofan I).inj i ≫ C.reindex (id : I → I) ≫
    solve ((Wiring.base (σ := σ) f).body C F.toFixpoints op) = _
  rw [C.reindex_inj_assoc, C.reindex_inj]
  exact (solution_row F C op (Wiring.base f) i).trans (by
    simp [Wiring.base, Wiring.branch, Wiring.interpretation, Interpretation.branch])

theorem evaluate_generator (a : σ.Symbol) :
    (Wiring.generator a).evaluate C F.toFixpoints op = Term.evaluate C F.toFixpoints op (.generator a) := by
  let g := Wiring.generator (σ := σ) a
  let picked := solve (g.body C F.toFixpoints op)
  have args : C.reindex (Sum.inr : Arity.ofNat (σ.arity a) → g.states) ≫ picked = 𝟙 _ := by
    apply Cofan.IsColimit.hom_ext (C.colimit (Arity.ofNat (σ.arity a)))
    intro i
    rw [C.reindex_inj_assoc, Category.comp_id]
    exact (solution_row F C op g (Sum.inr i)).trans (by
      simp [g, Wiring.generator, Wiring.branch, Wiring.interpretation, Interpretation.branch])
  apply Cofan.IsColimit.hom_ext (C.colimit Arity.one)
  intro i
  change (C.cofan Arity.one).inj i ≫ C.reindex g.entry ≫ picked = _
  rw [C.reindex_inj_assoc, Term.evaluate_generator]
  refine (solution_row F C op g (Sum.inl i)).trans ?_
  change (op a ≫ C.reindex (Sum.inr : Arity.ofNat (σ.arity a) → g.states) ≫ P.inr) ≫
    P.desc (𝟙 _) picked = _
  simp only [Category.assoc, P.inr_desc]
  rw [args, Category.comp_id]

private theorem branch_connect {S T R : Arity} {Y : K}
    (ren : S → T) (redirect : E → Instruction σ R T)
    (k : P.sum (C.cofan R).pt (C.cofan T).pt ⟶ Y)
    (exits : (C.cofan E).pt ⟶ Y) (states : (C.cofan S).pt ⟶ Y)
    (hexit : ∀ e, Wiring.branch C F.toFixpoints op (redirect e) ≫ k =
      (C.cofan E).inj e ≫ exits)
    (hstate : C.reindex ren ≫ P.inr ≫ k = states)
    (row : Instruction σ E S) :
    Wiring.branch C F.toFixpoints op (row.connect ren redirect) ≫ k =
      Wiring.branch C F.toFixpoints op row ≫ P.desc exits states := by
  cases row with
  | jump s =>
    simp only [Instruction.connect, Wiring.branch, Category.assoc, P.inr_desc]
    rw [← hstate, C.reindex_inj_assoc]
  | head row =>
    cases row with
    | bottom =>
      simp only [Instruction.connect, Wiring.branch, Interpretation.branch, Wiring.interpretation,
        Category.assoc, P.inl_desc]
      exact (bottom_natural F _).trans (bottom_natural F _).symm
    | exit e =>
      simpa only [Instruction.connect, Wiring.branch, Interpretation.branch, Wiring.interpretation,
        Category.assoc, P.inl_desc] using hexit e
    | node a child =>
      simp only [Instruction.connect, Wiring.branch, Interpretation.branch, Wiring.interpretation,
        Category.assoc, P.inr_desc]
      rw [← C.reindex_comp child ren, Category.assoc, hstate]

private theorem reindex_inl_split (S T : Arity) :
    C.reindex (Sum.inl : S → S.sum T) ≫ C.split P S T = P.inl := by
  apply Cofan.IsColimit.hom_ext (C.colimit S)
  intro s
  rw [C.reindex_inj_assoc, C.inj_inl_split]

private theorem reindex_inr_split (S T : Arity) :
    C.reindex (Sum.inr : T → S.sum T) ≫ C.split P S T = P.inr := by
  apply Cofan.IsColimit.hom_ext (C.colimit T)
  intro t
  rw [C.reindex_inj_assoc, C.inj_inr_split]

theorem evaluate_iterate (g : Wiring σ I (E.sum I)) :
    g.iterate.evaluate C F.toFixpoints op =
      solve (g.evaluate C F.toFixpoints op ≫ C.split P E I) := by
  let entry := C.reindex g.entry
  let split := C.split P E I
  let b := g.body C F.toFixpoints op ≫ P.map split (𝟙 (C.cofan g.states).pt)
  let out := P.desc (P.map (𝟙 (C.cofan E).pt) entry) P.inr
  have rows : g.iterate.body C F.toFixpoints op = b ≫ out := by
    apply Cofan.IsColimit.hom_ext (C.colimit g.states)
    intro s
    refine (body_row F C op g.iterate (show g.iterate.states from s)).trans ?_
    change Wiring.branch C F.toFixpoints op ((g.row s).connect id _) =
      (C.cofan g.states).inj s ≫
        (g.body C F.toFixpoints op ≫ P.map split (𝟙 (C.cofan g.states).pt)) ≫ out
    rw [← Category.assoc, ← Category.assoc, body_row, Category.assoc]
    cases g.row s with
    | jump t => simp [Wiring.branch, Instruction.connect, out, Coproducts.map]
    | head row =>
      cases row with
      | bottom =>
        simp only [Instruction.connect, Wiring.branch, Interpretation.branch, Wiring.interpretation,
          Category.assoc, Coproducts.map_desc, P.inl_desc, out]
        calc
          _ = solve (P.inr (X := P.sum (C.cofan E).pt (C.cofan g.states).pt) (Y := X)) :=
            bottom_natural F _
          _ = _ := (bottom_natural F _).symm
      | exit e =>
        cases e with
        | inl e =>
          simp [Instruction.connect, Wiring.branch, Interpretation.branch, Wiring.interpretation,
            split, out, Coproducts.map]
        | inr i =>
          simp [Instruction.connect, Wiring.branch, Interpretation.branch, Wiring.interpretation,
            split, out, Coproducts.map, entry]
      | node a child =>
        simp [Instruction.connect, Wiring.branch, Interpretation.branch, Wiring.interpretation,
          out, Coproducts.map]
  have inner : solve b = solve (g.body C F.toFixpoints op) ≫ split :=
    F.naturalCodiagonal.naturality _ split True.intro True.intro
  change entry ≫ solve (g.iterate.body C F.toFixpoints op) =
    solve ((entry ≫ solve (g.body C F.toFixpoints op)) ≫ split)
  calc
    _ = entry ≫ solve (b ≫ out) := congrArg
      (fun body : (C.cofan g.states).pt ⟶ P.sum (C.cofan E).pt (C.cofan g.states).pt =>
        entry ≫ solve body) rows
    _ = solve (entry ≫ solve b) := feedback_rewire F b entry
    _ = solve (entry ≫ solve (g.body C F.toFixpoints op) ≫ split) :=
      congrArg (fun k : (C.cofan g.states).pt ⟶ P.sum (C.cofan E).pt (C.cofan I).pt =>
        solve (entry ≫ k)) inner
    _ = _ := congrArg
      (fun k : (C.cofan I).pt ⟶ P.sum (C.cofan E).pt (C.cofan I).pt => solve k)
      (Category.assoc _ _ _).symm

theorem evaluate_comp {J : Arity} (f : Wiring σ I J) (g : Wiring σ J E) :
    (f.comp g).evaluate C F.toFixpoints op =
      f.evaluate C F.toFixpoints op ≫ g.evaluate C F.toFixpoints op := by
  let S := (C.cofan f.states).pt
  let T := (C.cofan g.states).pt
  let R := (C.cofan E).pt
  let iso := C.sumIso P f.states g.states
  let next := C.reindex g.entry
  let a := f.body C F.toFixpoints op
  let b := g.body C F.toFixpoints op
  let left : S ⟶ P.sum (P.sum R S) T := a ≫ P.desc (next ≫ P.inr) (P.inr ≫ P.inl)
  let right : T ⟶ P.sum (P.sum R S) T := b ≫ P.map P.inl (𝟙 T)
  let flat := P.desc left right ≫ P.assoc
  let transport := P.map (𝟙 R) iso.hom
  have hleft : left ≫ P.assoc = a ≫ P.desc (next ≫ P.inr ≫ P.inr) (P.inl ≫ P.inr) := by
    simp [left, Coproducts.assoc]
  have hright : right ≫ P.assoc = b ≫ P.desc P.inl (P.inr ≫ P.inr) := by
    simp [right, T, Coproducts.assoc]
  have square : iso.hom ≫ flat = (f.comp g).body C F.toFixpoints op ≫ transport := by
    apply Cofan.IsColimit.hom_ext (C.colimit (f.states.sum g.states))
    rintro (s | t)
    · have row := body_row F C op (f.comp g) (.inl s)
      change (C.cofan (f.states.sum g.states)).inj (.inl s) ≫
        C.split P f.states g.states ≫ flat =
        (C.cofan (f.states.sum g.states)).inj (.inl s) ≫ (f.comp g).body C F.toFixpoints op ≫ transport
      rw [C.inj_inl_split_assoc, ← Category.assoc _ ((f.comp g).body C F.toFixpoints op) transport, row]
      change (C.cofan f.states).inj s ≫ P.inl ≫ flat =
        Wiring.branch C F.toFixpoints op
          ((f.row s).connect Sum.inl (fun j => .jump (Sum.inr (g.entry j)))) ≫ transport
      simp only [flat, P.inl_desc_assoc, hleft, a, ← Category.assoc ((C.cofan f.states).inj s), body_row]
      apply Eq.symm
      refine branch_connect F C op Sum.inl (fun j => .jump (Sum.inr (g.entry j)))
        transport (next ≫ P.inr ≫ P.inr) (P.inl ≫ P.inr) ?_ ?_ (f.row s)
      · intro j
        simp [Wiring.branch, transport, iso, FiniteCopowers.sumIso, next, Coproducts.map]
      · simp [transport, iso, FiniteCopowers.sumIso, Coproducts.map, ← Category.assoc, reindex_inl_split C]
    · have row := body_row F C op (f.comp g) (.inr t)
      change (C.cofan (f.states.sum g.states)).inj (.inr t) ≫
        C.split P f.states g.states ≫ flat =
        (C.cofan (f.states.sum g.states)).inj (.inr t) ≫ (f.comp g).body C F.toFixpoints op ≫ transport
      rw [C.inj_inr_split_assoc, ← Category.assoc _ ((f.comp g).body C F.toFixpoints op) transport, row]
      change (C.cofan g.states).inj t ≫ P.inr ≫ flat =
        Wiring.branch C F.toFixpoints op
          ((g.row t).connect Sum.inr (fun e => .head (.exit e))) ≫ transport
      simp only [flat, P.inr_desc_assoc, hright, b, ← Category.assoc ((C.cofan g.states).inj t), body_row]
      apply Eq.symm
      refine branch_connect F C op Sum.inr (fun e => .head (.exit e))
        transport P.inl (P.inr ≫ P.inr) ?_ ?_ (g.row t)
      · intro e
        simp [Wiring.branch, Wiring.interpretation, Interpretation.branch, transport, Coproducts.map]
      · simp [transport, iso, FiniteCopowers.sumIso, Coproducts.map, ← Category.assoc, reindex_inr_split C]
  have entry : C.reindex (f.comp g).entry ≫ iso.hom = C.reindex f.entry ≫ P.inl := by
    change C.reindex (Sum.inl ∘ f.entry) ≫ C.split P f.states g.states = _
    rw [← C.reindex_comp, Category.assoc, reindex_inl_split C]
  calc
    _ = C.reindex (f.comp g).entry ≫ iso.hom ≫ solve flat := congrArg
      (fun k : (C.cofan (f.states.sum g.states)).pt ⟶ R => C.reindex (f.comp g).entry ≫ k)
      (F.uniform_iso iso _ flat True.intro True.intro square).symm
    _ = C.reindex f.entry ≫ (P.inl ≫ solve flat) := by rw [← Category.assoc, entry, Category.assoc]
    _ = _ := by
      have stages : P.inl ≫ solve flat = solve a ≫ next ≫ solve b :=
        staged_comp F a b next
      rw [stages]
      simp only [Wiring.evaluate, Category.assoc, a, next, b]

theorem evaluate_pair {J : Arity} (f : Wiring σ I E) (g : Wiring σ J E) :
    (f.pair g).evaluate C F.toFixpoints op =
      C.split P I J ≫ P.desc (f.evaluate C F.toFixpoints op) (g.evaluate C F.toFixpoints op) := by
  let R := (C.cofan E).pt
  let iso := C.sumIso P f.states g.states
  let a := f.body C F.toFixpoints op
  let b := g.body C F.toFixpoints op
  let flat := P.desc (a ≫ P.map (𝟙 R) P.inl) (b ≫ P.map (𝟙 R) P.inr)
  let transport := P.map (𝟙 R) iso.hom
  have square : iso.hom ≫ flat = (f.pair g).body C F.toFixpoints op ≫ transport := by
    apply Cofan.IsColimit.hom_ext (C.colimit (f.states.sum g.states))
    rintro (s | t)
    · have row := body_row F C op (f.pair g) (.inl s)
      change (C.cofan (f.states.sum g.states)).inj (.inl s) ≫
        C.split P f.states g.states ≫ flat =
        (C.cofan (f.states.sum g.states)).inj (.inl s) ≫ (f.pair g).body C F.toFixpoints op ≫ transport
      rw [C.inj_inl_split_assoc, ← Category.assoc _ ((f.pair g).body C F.toFixpoints op) transport, row]
      change (C.cofan f.states).inj s ≫ P.inl ≫ flat =
        Wiring.branch C F.toFixpoints op
          ((f.row s).connect Sum.inl (fun e => .head (.exit e))) ≫ transport
      dsimp only [flat, a]
      rw [P.inl_desc, ← Category.assoc, body_row]
      simp only [Coproducts.map, R, Category.id_comp]
      apply Eq.symm
      refine branch_connect F C op Sum.inl (fun e => .head (.exit e))
        transport P.inl (P.inl ≫ P.inr) ?_ ?_ (f.row s)
      · intro e
        simp [Wiring.branch, Wiring.interpretation, Interpretation.branch, transport, Coproducts.map]
      · simp [transport, iso, FiniteCopowers.sumIso, Coproducts.map, ← Category.assoc, reindex_inl_split C]
    · have row := body_row F C op (f.pair g) (.inr t)
      change (C.cofan (f.states.sum g.states)).inj (.inr t) ≫
        C.split P f.states g.states ≫ flat =
        (C.cofan (f.states.sum g.states)).inj (.inr t) ≫ (f.pair g).body C F.toFixpoints op ≫ transport
      rw [C.inj_inr_split_assoc, ← Category.assoc _ ((f.pair g).body C F.toFixpoints op) transport, row]
      change (C.cofan g.states).inj t ≫ P.inr ≫ flat =
        Wiring.branch C F.toFixpoints op
          ((g.row t).connect Sum.inr (fun e => .head (.exit e))) ≫ transport
      dsimp only [flat, b]
      rw [P.inr_desc, ← Category.assoc, body_row]
      simp only [Coproducts.map, R, Category.id_comp]
      apply Eq.symm
      refine branch_connect F C op Sum.inr (fun e => .head (.exit e))
        transport P.inl (P.inr ≫ P.inr) ?_ ?_ (g.row t)
      · intro e
        simp [Wiring.branch, Wiring.interpretation, Interpretation.branch, transport, Coproducts.map]
      · simp [transport, iso, FiniteCopowers.sumIso, Coproducts.map, ← Category.assoc, reindex_inr_split C]
  have both : solve ((f.pair g).body C F.toFixpoints op) = iso.hom ≫ solve flat :=
    (F.uniform_iso iso _ flat True.intro True.intro square).symm
  have hl : P.inl ≫ solve flat = solve a :=
    F.uniform_inl a flat True.intro True.intro (P.inl_desc _ _)
  have hr : P.inr ≫ solve flat = solve b :=
    F.uniform_inr b flat True.intro True.intro (P.inr_desc _ _)
  change C.reindex (Sum.map f.entry g.entry) ≫ solve ((f.pair g).body C F.toFixpoints op) = _
  have start : C.reindex (Sum.map f.entry g.entry) ≫ iso.hom =
      C.split P I J ≫ P.map (C.reindex f.entry) (C.reindex g.entry) := by
    apply Cofan.IsColimit.hom_ext (C.colimit (I.sum J))
    rintro (i | j)
    · simpa [iso, FiniteCopowers.sumIso, Coproducts.map] using
        (C.inj_inl_split (P := P) (J := g.states) (f.entry i))
    · simpa [iso, FiniteCopowers.sumIso, Coproducts.map] using
        (C.inj_inr_split (P := P) (I := f.states) (g.entry j))
  have finish : P.map (C.reindex f.entry) (C.reindex g.entry) ≫ solve flat =
      P.desc (f.evaluate C F.toFixpoints op) (g.evaluate C F.toFixpoints op) := by
    simp [Coproducts.map, hl, hr, Wiring.evaluate, a, b]
  calc
    _ = C.reindex (Sum.map f.entry g.entry) ≫ (iso.hom ≫ solve flat) :=
      congrArg (fun k : (C.cofan (f.states.sum g.states)).pt ⟶ R =>
        C.reindex (Sum.map f.entry g.entry) ≫ k) both
    _ = _ := by rw [← Category.assoc, start, Category.assoc, finish]

theorem term_evaluation (term : Term σ I E) :
    term.wiring.evaluate C F.toFixpoints op = term.evaluate C F.toFixpoints op := by
  induction term with
  | base f => exact evaluate_base F C op f
  | generator a => exact evaluate_generator F C op a
  | pair f g hf hg =>
    change (f.wiring.pair g.wiring).evaluate C F.toFixpoints op =
      C.split P _ _ ≫ P.desc (f.evaluate C F.toFixpoints op) (g.evaluate C F.toFixpoints op)
    rw [evaluate_pair F, hf, hg]
  | comp f g hf hg =>
    change (f.wiring.comp g.wiring).evaluate C F.toFixpoints op =
      f.evaluate C F.toFixpoints op ≫ g.evaluate C F.toFixpoints op
    rw [evaluate_comp F, hf, hg]
  | iterate f hf =>
    refine (evaluate_iterate F C op f.wiring).trans ?_
    exact congrArg (fun k => solve (k ≫ C.split P _ _)) hf

end Silmaril.Calco2019.Proofs.IterationWiringEvaluation
