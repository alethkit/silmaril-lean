module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.Observation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms

/-! # Separation and reconstruction for finite unit coproducts -/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithConstructorSequencing Paper.WithConstructorSequencing.UnitSumSquare
open Paper.UnaryReturn.Beta.Constructors (Normalizes)
open Paper.TypeCategory CategoryTheory CategoryTheory.Limits
open Paper.BoundSimulation (boundReturn)
open scoped Paper.BoundSimulation.Obstruction

set_option backward.isDefEq.respectTransparency false

private abbrev replaceZero (a : Tm Empty) := Tm.consSubst a (Tm.var ∘ Nat.succ)

private theorem replaceZero_typed {A B : Ty Empty} {a : Tm Empty}
    (ha : Tm.BranchValue [A] a B) :
    ∀ ⦃i : Nat⦄ ⦃X : Ty Empty⦄, At [B] i X → Tm.BranchValue [A] (replaceZero a i) X := by
  intro i X hi
  cases i with
  | zero => cases Option.some.inj hi; exact ha
  | succ i => cases i <;> contradiction

private theorem branch_comp {A B C : Ty Empty} {a b : Tm Empty}
    (ha : Tm.BranchValue [A] a B) (hb : Tm.BranchValue [B] b C) :
    branch ha ≫ branch hb = branch (hb.subst (σ := replaceZero a) (replaceZero_typed ha)) := by
  let hr := (CfgEta.TypeCategory.seqValueBranches (.br (ℓ := 0) rfl ha) (.br (ℓ := 0) rfl hb))
  unfold branch
  rw [ofRegion_comp _ _ hr, ofRegion_eq_iff]
  have e : compLSubst (fun _ => Region.br 0 a) (fun _ => Region.br 0 b) 0 =
      Region.br 0 (b.subst (replaceZero a)) := by
    have hz : Tm.singleSubst a ∘ Silmaril.DeBruijn.lift Nat.succ = replaceZero a := by
      funext i
      cases i <;> rfl
    simp only [compLSubst, lsubst, liftLSubstVars, substVars_renameVars, hz, Region.substVars]
  exact e.symm ▸ Paper.Eqv.refl (.br rfl (hb.subst (σ := replaceZero a) (replaceZero_typed ha)).hasType)

private theorem branch_congr {A B : Ty Empty} {a b : Tm Empty}
    (ha : Tm.BranchValue [A] a B) (hb : Tm.BranchValue [A] b B) (e : a = b) :
    branch ha = branch hb := by subst b; rfl

private theorem tag_subst (A : Shape) (i : A.Row) (a : Tm Empty) (θ : Nat → Tm Empty) :
    (A.tagTerm i a).subst θ = A.tagTerm i (a.subst θ) := by
  induction A with
  | empty => exact i.elim
  | unit => rfl
  | sum A B il ir =>
    cases i with
    | inl i => exact congrArg Tm.inl (il i)
    | inr i => exact congrArg Tm.inr (ir i)

private theorem tag_inl (A B : Shape) (i : A.Row) {a : Tm Empty}
    (ha : Tm.BranchValue [(Ty.unit : Ty Empty)] a .unit) :
    branch (A.tagValue i ha) ≫ (sumCofan A.ty B.ty).inl =
      branch ((Shape.sum A B).tagValue (.inl i) ha) := by
  rw [sumCofan_inl]
  exact branch_comp (A.tagValue i ha) (.inl (.var (i := 0) rfl))

private theorem tag_inr (A B : Shape) (i : B.Row) {a : Tm Empty}
    (ha : Tm.BranchValue [(Ty.unit : Ty Empty)] a .unit) :
    branch (B.tagValue i ha) ≫ (sumCofan A.ty B.ty).inr =
      branch ((Shape.sum A B).tagValue (.inr i) ha) := by
  rw [sumCofan_inr]
  exact branch_comp (B.tagValue i ha) (.inr (.var (i := 0) rfl))

theorem inj_table (A : Shape) {X : Paper.TypeCategory Empty} (rows : A.Row → (obj .unit ⟶ X))
    (i : A.Row) : A.inj i ≫ A.table rows = rows i := by
  induction A with
  | empty => exact i.elim
  | unit => cases i; rw [Shape.inj, Shape.table, branch, ofRegion_id, Category.id_comp]
  | sum A B ihA ihB =>
    cases i with
    | inl i =>
      change branch ((Shape.sum A B).tagValue (.inl i) (.var (i := 0) rfl)) ≫ _ = _
      rw [← tag_inl A B i (.var (i := 0) rfl), Shape.table, Category.assoc, ← Category.assoc (sumCofan A.ty B.ty).inl,
        sumCofan_inl_sumIso_hom, coprod.inl_desc]
      exact ihA _ i
    | inr i =>
      change branch ((Shape.sum A B).tagValue (.inr i) (.var (i := 0) rfl)) ≫ _ = _
      rw [← tag_inr A B i (.var (i := 0) rfl), Shape.table, Category.assoc, ← Category.assoc (sumCofan A.ty B.ty).inr,
        sumCofan_inr_sumIso_hom, coprod.inr_desc]
      exact ihB _ i

theorem table_hom_ext (A : Shape) {X : Paper.TypeCategory Empty} {f g : obj A.ty ⟶ X}
    (h : ∀ i : A.Row, A.inj i ≫ f = A.inj i ≫ g) : f = g := by
  induction A with
  | empty =>
    obtain ⟨_, hf, rfl⟩ := exists_ofRegion f
    obtain ⟨_, hg, rfl⟩ := exists_ofRegion g
    exact (ofRegion_eq_iff hf hg).mpr (.cfgEta (.native
      (SubstitutionEquiv.initial_var (i := 0) rfl hf.hasType hg.hasType)))
  | unit =>
    simpa only [Shape.inj, Shape.tagValue, branch, ofRegion_id, Category.id_comp] using h ()
  | sum A B ihA ihB =>
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit A.ty B.ty)
    · apply ihA
      intro i
      rw [← Category.assoc, ← Category.assoc, show A.inj i ≫ (sumCofan A.ty B.ty).inl =
        (Shape.sum A B).inj (.inl i) from tag_inl A B i (.var (i := 0) rfl)]
      exact h (.inl i)
    · apply ihB
      intro i
      rw [← Category.assoc, ← Category.assoc, show B.inj i ≫ (sumCofan A.ty B.ty).inr =
        (Shape.sum A B).inj (.inr i) from tag_inr A B i (.var (i := 0) rfl)]
      exact h (.inr i)

private theorem tag_injective (A : Shape) {i j : A.Row} {a b : Tm Empty}
    (eq : A.tagTerm i a = A.tagTerm j b) : i = j ∧ a = b := by
  induction A with
  | empty => exact i.elim
  | unit => cases i; cases j; exact ⟨rfl, eq⟩
  | sum A B ihA ihB =>
    cases i <;> cases j
    · obtain ⟨e, h⟩ := ihA (Tm.inl.inj eq)
      exact ⟨congrArg Sum.inl e, h⟩
    · cases eq
    · cases eq
    · obtain ⟨e, h⟩ := ihB (Tm.inr.inj eq)
      exact ⟨congrArg Sum.inr e, h⟩

private theorem payload_observation_injective :
    Function.Injective (fun p : Payload => p.term.subst (fun _ => .inl .unit)) := by
  intro p q h
  cases p <;> cases q <;> first | rfl | cases h

theorem separate_payload_output (B A : Shape) {i j : OutputCode B A}
    (h : projection.map (outputWithPayload B A i) = projection.map (outputWithPayload B A j)) :
    i = j := by
  rw [outputWithPayload, outputWithPayload, projection.map_comp, projection.map_comp] at h
  have e := (cancel_mono (projection.map (sumIso B.ty A.ty).hom)).mp h
  let vi := (Shape.sum B A).tagValue i.tag i.payload.value
  let vj := (Shape.sum B A).tagValue j.tag j.payload.value
  have eq := (Paper.Extension.Singleton.ofRegion_eq_iff Seed
    (.br (ℓ := 0) rfl vi) (.br (ℓ := 0) rfl vj)).mp e
  obtain ⟨literal, alternate⟩ :=
    Paper.BoundSimulation.Obstruction.PairSequencing.unit_branch_observations vi vj eq
  rw [tag_subst, tag_subst] at literal alternate
  have tag := (tag_injective (.sum B A) literal).1
  have payload := payload_observation_injective (tag_injective (.sum B A) alternate).2
  cases i
  cases j
  cases tag
  cases payload
  rfl

theorem separate_output (B A : Shape) {i j : Sum B.Row A.Row}
    (h : projection.map (output B A i) = projection.map (output B A j)) : i = j :=
  congrArg OutputCode.tag
    (separate_payload_output B A (i := ⟨i, .literal⟩) (j := ⟨j, .literal⟩) h)

private theorem unit_slot {i : Nat} {A : Ty Empty} (hi : At [.unit] i A) :
    i = 0 ∧ A = .unit := by
  cases i with
  | zero => exact ⟨rfl, (Option.some.inj hi).symm⟩
  | succ i => cases i <;> contradiction

private theorem tagged_unit (A : Shape) {a : Tm Empty} (ha : Tm.BranchValue [(Ty.unit : Ty Empty)] a A.ty) :
    ∃ j : A.Row, a = A.tagTerm j (.var 0) ∨ a = A.tagTerm j .unit := by
  induction A generalizing a with
  | empty =>
    change Tm.BranchValue [(Ty.unit : Ty Empty)] a .empty at ha
    cases ha with
    | var hi => cases (unit_slot hi).2
  | unit =>
    change Tm.BranchValue [(Ty.unit : Ty Empty)] a .unit at ha
    cases ha with
    | var hi => rw [(unit_slot hi).1]; exact ⟨(), .inl rfl⟩
    | unit => exact ⟨(), .inr rfl⟩
  | sum A B ihA ihB =>
    change Tm.BranchValue [(Ty.unit : Ty Empty)] a (.coprod A.ty B.ty) at ha
    cases ha with
    | var hi => cases (unit_slot hi).2
    | inl ha =>
      obtain ⟨j, rfl | rfl⟩ := ihA ha
      · exact ⟨.inl j, .inl rfl⟩
      · exact ⟨.inl j, .inr rfl⟩
    | inr ha =>
      obtain ⟨j, rfl | rfl⟩ := ihB ha
      · exact ⟨.inr j, .inl rfl⟩
      · exact ⟨.inr j, .inr rfl⟩

private theorem row_image (A D : Shape) (i : A.Row) {a : Tm Empty}
    (ha : Tm.BranchValue [A.ty] a D.ty) :
    ∃ (j : D.Row) (p : Payload), A.inj i ≫ branch ha = D.emit j p := by
  unfold Shape.inj
  rw [branch_comp]
  obtain ⟨j, h | h⟩ := tagged_unit D (ha.subst (σ := replaceZero (A.tagTerm i (.var 0)))
    (replaceZero_typed (A.tagValue i (.var (i := 0) rfl))))
  · exact ⟨j, .forward, branch_congr _ _ h⟩
  · exact ⟨j, .literal, branch_congr _ _ h⟩

private noncomputable abbrev literalUnit : obj .unit ⟶ obj .unit := Shape.unit.literal ()

private theorem literal_factor (A : Shape) (i : A.Row) :
    literalUnit ≫ A.inj i = A.literal i := by
  unfold literalUnit Shape.inj Shape.literal
  rw [branch_comp]
  exact branch_congr _ _ (tag_subst A i (.var 0) (replaceZero .unit))

private theorem literal_stable (A : Shape) (i : A.Row) :
    literalUnit ≫ A.literal i = A.literal i := by
  unfold literalUnit Shape.literal
  rw [branch_comp]
  exact branch_congr _ _ (tag_subst A i .unit (replaceZero .unit))

private theorem output_inr (B A : Shape) (i : A.Row) :
    output B A (.inr i) = A.literal i ≫ coprod.inr := by
  rw [output, ← sumCofan_inr_sumIso_hom B.ty A.ty, ← Category.assoc]
  exact congrArg (· ≫ (sumIso B.ty A.ty).hom) (tag_inr B A i .unit).symm

private theorem payload_before_emit (A : Shape) (i : A.Row) (p q : Payload) :
    Shape.unit.emit () p ≫ A.emit i q = A.emit i (p.then q) := by
  unfold Shape.emit
  rw [branch_comp]
  apply branch_congr
  rw [tag_subst]
  cases p <;> cases q <;> rfl

private theorem emit_factor (A : Shape) (i : A.Row) (p : Payload) :
    Shape.unit.emit () p ≫ A.inj i = A.emit i p :=
  payload_before_emit A i p .forward

private theorem payload_output_inl (B A : Shape) (i : B.Row) (p : Payload) :
    outputWithPayload B A ⟨.inl i, p⟩ = B.emit i p ≫ coprod.inl := by
  rw [outputWithPayload, ← sumCofan_inl_sumIso_hom B.ty A.ty, ← Category.assoc]
  exact congrArg (· ≫ (sumIso B.ty A.ty).hom) (tag_inl B A i p.value).symm

private theorem payload_output_inr (B A : Shape) (i : A.Row) (p : Payload) :
    outputWithPayload B A ⟨.inr i, p⟩ = A.emit i p ≫ coprod.inr := by
  rw [outputWithPayload, ← sumCofan_inr_sumIso_hom B.ty A.ty, ← Category.assoc]
  exact congrArg (· ≫ (sumIso B.ty A.ty).hom) (tag_inr B A i p.value).symm

private theorem payload_before_output (B A : Shape) (p : Payload) (o : OutputCode B A) :
    Shape.unit.emit () p ≫ outputWithPayload B A o =
      outputWithPayload B A ⟨o.tag, p.then o.payload⟩ := by
  rw [outputWithPayload, outputWithPayload, ← Category.assoc, payload_before_emit]

private theorem map_recurrence (B A D : Shape) {a : Tm Empty} (ha : Tm.BranchValue [A.ty] a D.ty)
    {i : A.Row} {j : D.Row} {p : Payload} (h : A.inj i ≫ branch ha = D.emit j p) (q : Payload) :
    outputWithPayload B A ⟨.inr i, q⟩ ≫ coprod.map (𝟙 (obj B.ty)) (branch ha) =
      outputWithPayload B D ⟨.inr j, q.then p⟩ := by
  have next : A.emit i q ≫ branch ha = D.emit j (q.then p) := by
    rw [← emit_factor, Category.assoc, h, payload_before_emit]
  rw [payload_output_inr, payload_output_inr, Category.assoc, coprod.inr_map, ← Category.assoc, next]

private theorem source_row (B A D : Shape) {a : Tm Empty} (ha : Tm.BranchValue [A.ty] a D.ty)
    (o : OutputCode B A) :
    ∃ o' : OutputCode B D, outputWithPayload B A o ≫ coprod.map (𝟙 (obj B.ty)) (branch ha) =
      outputWithPayload B D o' := by
  rcases o with ⟨i | i, p⟩
  · exact ⟨⟨.inl i, p⟩, by simp [payload_output_inl]⟩
  · obtain ⟨j, q, h⟩ := row_image A D i ha
    exact ⟨_, map_recurrence B A D ha h p⟩

private theorem table_after_state (B A D : Shape) {a : Tm Empty}
    (ha : Tm.BranchValue [A.ty] a D.ty)
    (q : D.Row → (obj .unit ⟶ obj B.ty ⨿ obj D.ty))
    {i : A.Row} {j : D.Row} {p : Payload} (h : A.inj i ≫ branch ha = D.emit j p)
    {o : OutputCode B D} (ho : q j = outputWithPayload B D o) :
    A.inj i ≫ (branch ha ≫ D.table q) = outputWithPayload B D ⟨o.tag, p.then o.payload⟩ := by
  rw [← Category.assoc, h, ← emit_factor, Category.assoc, inj_table, ho, payload_before_output]

private theorem target_row (B A D : Shape) {a : Tm Empty} (ha : Tm.BranchValue [A.ty] a D.ty)
    (q : D.Row → (obj .unit ⟶ obj B.ty ⨿ obj D.ty)) (hq : HasTargetOutputs B A D ha q)
    (i : A.Row) :
    ∃ o : OutputCode B D, A.inj i ≫ (branch ha ≫ D.table q) = outputWithPayload B D o := by
  obtain ⟨j, p, h⟩ := row_image A D i ha
  obtain ⟨o, ho⟩ := hq i j p h
  exact ⟨_, table_after_state B A D ha q h ho⟩

theorem reflect_payload_square (B A D : Shape) {a : Tm Empty} (ha : Tm.BranchValue [A.ty] a D.ty)
    (p : A.Row → OutputCode B A) (q : D.Row → (obj .unit ⟶ obj B.ty ⨿ obj D.ty))
    (hq : HasTargetOutputs B A D ha q)
    (comm : projection.map (stepWithPayload B A p ≫ coprod.map (𝟙 (obj B.ty)) (branch ha)) =
      projection.map (branch ha ≫ D.table q)) :
    stepWithPayload B A p ≫ coprod.map (𝟙 (obj B.ty)) (branch ha) = branch ha ≫ D.table q := by
  apply table_hom_ext A
  intro i
  obtain ⟨o, ho⟩ := source_row B A D ha (p i)
  obtain ⟨j, hj⟩ := target_row B A D ha q hq i
  have hi : A.inj i ≫ (stepWithPayload B A p ≫ coprod.map (𝟙 (obj B.ty)) (branch ha)) =
      outputWithPayload B D o := by
    rw [← Category.assoc, stepWithPayload, inj_table]
    exact ho
  have h := congrArg (projection.map (A.inj i) ≫ ·) comm
  rw [← projection.map_comp, ← projection.map_comp, hi, hj] at h
  rw [hi, hj, separate_payload_output B D h]

private theorem literal_targets (B A D : Shape) {a : Tm Empty} (ha : Tm.BranchValue [A.ty] a D.ty)
    (q : D.Row → (obj .unit ⟶ obj B.ty ⨿ obj D.ty)) (hq : HasLiteralTargets B A D ha q) :
    HasTargetOutputs B A D ha q := by
  intro i j p h
  have hit : A.inj i ≫ branch ha = D.inj j ∨ A.inj i ≫ branch ha = D.literal j := by
    cases p
    · exact .inl h
    · exact .inr h
  obtain ⟨o, ho⟩ := hq i j hit
  exact ⟨⟨o, .literal⟩, ho⟩

theorem reflect_square (B A D : Shape) {a : Tm Empty} (ha : Tm.BranchValue [A.ty] a D.ty)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → (obj .unit ⟶ obj B.ty ⨿ obj D.ty))
    (hq : HasLiteralTargets B A D ha q)
    (comm : projection.map (step B A p ≫ coprod.map (𝟙 (obj B.ty)) (branch ha)) =
      projection.map (branch ha ≫ D.table q)) :
    step B A p ≫ coprod.map (𝟙 (obj B.ty)) (branch ha) = branch ha ≫ D.table q :=
  reflect_payload_square B A D ha (fun i => ⟨p i, .literal⟩) q (literal_targets B A D ha q hq) comm

private theorem project_update {A D : Shape} {t c : Tm Empty}
    (hc : Normalizes [A.ty] t c D.ty) :
    projection.map (boundReturn hc.typed.1) = projection.map (branch hc.typed.2) :=
  (Paper.Extension.Singleton.ofRegion_eq_iff Seed
    (Paper.RetainedLet.returnOnce_typed hc.typed.1) (.br (ℓ := 0) rfl hc.typed.2)).mpr
    (returnOnce_eq_branch hc)

private theorem project_update_coprod_map (B : Shape) {A D : Shape} {t c : Tm Empty}
    (hc : Normalizes [A.ty] t c D.ty) :
    projection.map (coprod.map (𝟙 (obj B.ty)) (boundReturn hc.typed.1)) =
      projection.map (coprod.map (𝟙 (obj B.ty)) (branch hc.typed.2)) :=
  Paper.Extension.Singleton.projection_map_coprod_map_congr Seed rfl (project_update hc)

theorem iterate_payload_uniformity (B A D : Shape) {t c : Tm Empty}
    (hc : Normalizes [A.ty] t c D.ty)
    (p : A.Row → OutputCode B A) (q : D.Row → (obj .unit ⟶ obj B.ty ⨿ obj D.ty))
    (hq : HasTargetOutputs B A D hc.typed.2 q)
    {f : obj A.ty ⟶ obj B.ty ⨿ obj A.ty} {g : obj D.ty ⟶ obj B.ty ⨿ obj D.ty}
    (hf : projection.map f = projection.map (stepWithPayload B A p))
    (hg : projection.map g = projection.map (D.table q))
    (comm : projection.map (f ≫ coprod.map (𝟙 (obj B.ty)) (boundReturn hc.typed.1)) =
      projection.map (boundReturn hc.typed.1 ≫ g)) :
    projection.map (iterate f) =
      projection.map (boundReturn hc.typed.1) ≫ projection.map (iterate g) := by
  apply hc.iterate_map_uniformity (fun h => .inl h) constructorSequencing hf hg
  apply reflect_payload_square B A D hc.typed.2 p q hq
  simpa only [Functor.map_comp, hf, hg, project_update_coprod_map B hc, project_update hc] using comm

theorem iterate_uniformity (B A D : Shape) {t c : Tm Empty}
    (hc : Normalizes [A.ty] t c D.ty)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → (obj .unit ⟶ obj B.ty ⨿ obj D.ty))
    (hq : HasLiteralTargets B A D hc.typed.2 q)
    {f : obj A.ty ⟶ obj B.ty ⨿ obj A.ty} {g : obj D.ty ⟶ obj B.ty ⨿ obj D.ty}
    (hf : projection.map f = projection.map (step B A p))
    (hg : projection.map g = projection.map (D.table q))
    (comm : projection.map (f ≫ coprod.map (𝟙 (obj B.ty)) (boundReturn hc.typed.1)) =
      projection.map (boundReturn hc.typed.1 ≫ g)) :
    projection.map (iterate f) =
      projection.map (boundReturn hc.typed.1) ≫ projection.map (iterate g) :=
  iterate_payload_uniformity B A D hc (fun i => ⟨p i, .literal⟩) q
    (literal_targets B A D hc.typed.2 q hq) hf hg comm

namespace Forwarding

open Paper.WithConstructorSequencing.UnitSumSquare.Forwarding

private theorem state_row (i : source.Row) :
    source.inj i ≫ branch normalizes.typed.2 = target.emit (.inl i) .forward :=
  branch_comp (source.tagValue i (.var (i := 0) rfl)) normalizes.typed.2

private theorem left_row (i : source.Row) :
    source.inj i ≫ (stepWithPayload result source sourceRows ≫
      coprod.map (𝟙 (obj result.ty)) (branch normalizes.typed.2)) =
      outputWithPayload result target (targetRows .forward (.inl i)) := by
  rw [← Category.assoc, stepWithPayload, inj_table]
  cases i with
  | inl i =>
    cases i
    exact map_recurrence result source target normalizes.typed.2 (state_row (.inr ())) .forward
  | inr i =>
    cases i
    change outputWithPayload result source ⟨.inl (), .forward⟩ ≫ _ =
      outputWithPayload result target ⟨.inl (), .forward⟩
    simp [payload_output_inl]

private theorem right_row (p : Payload) (i : source.Row) :
    source.inj i ≫ (branch normalizes.typed.2 ≫ stepWithPayload result target (targetRows p)) =
      outputWithPayload result target (targetRows p (.inl i)) := by
  have h := table_after_state result source target normalizes.typed.2
    (outputWithPayload result target ∘ targetRows p) (state_row i)
    (o := targetRows p (.inl i)) rfl
  have keep (q : Payload) : Payload.forward.then q = q := by cases q <;> rfl
  simpa only [stepWithPayload, keep] using h

private theorem square :
    stepWithPayload result source sourceRows ≫ coprod.map (𝟙 (obj result.ty)) (branch normalizes.typed.2) =
      branch normalizes.typed.2 ≫ stepWithPayload result target (targetRows .forward) := by
  apply table_hom_ext source
  intro i
  rw [left_row, right_row]

theorem iterate_forwarding :
    projection.map (iterate (stepWithPayload result source sourceRows)) =
      projection.map (boundReturn normalizes.typed.1) ≫
        projection.map (iterate (stepWithPayload result target (targetRows .forward))) := by
  apply iterate_payload_uniformity result source target normalizes sourceRows
    (outputWithPayload result target ∘ targetRows .forward)
    (fun _ j _ _ => ⟨targetRows .forward j, rfl⟩) rfl rfl
  rw [projection.map_comp, projection.map_comp,
    project_update_coprod_map result normalizes, project_update normalizes,
    ← projection.map_comp, ← projection.map_comp, square]
  rfl

theorem literal_square_fails :
    projection.map (stepWithPayload result source sourceRows ≫
      coprod.map (𝟙 (obj result.ty)) (boundReturn normalizes.typed.1)) ≠
      projection.map (boundReturn normalizes.typed.1 ≫ stepWithPayload result target (targetRows .literal)) := by
  intro comm
  rw [projection.map_comp, projection.map_comp,
    project_update_coprod_map result normalizes, project_update normalizes, ← projection.map_comp,
    ← projection.map_comp] at comm
  have h := congrArg (projection.map (source.inj (.inr ())) ≫ ·) comm
  rw [← projection.map_comp, ← projection.map_comp, left_row, right_row] at h
  have code := separate_payload_output result target h
  have payload : Payload.forward = Payload.literal := congrArg OutputCode.payload code
  cases payload

end Forwarding

namespace Collapse

open Paper.WithConstructorSequencing.UnitSumSquare.Collapse

private theorem collapse_row (i : source.Row) :
    source.inj i ≫ branch normalizes.typed.2 = target.literal (.inl ()) := by
  exact branch_comp (source.tagValue i (.var (i := 0) rfl)) normalizes.typed.2

theorem collapse_not_mono : ¬ Mono (branch normalizes.typed.2) := by
  intro hm
  have eq : source.inj (.inl ()) = source.inj (.inr ()) :=
    (cancel_mono (branch normalizes.typed.2)).mp
      ((collapse_row (.inl ())).trans (collapse_row (.inr ())).symm)
  have e := congrArg (literalUnit ≫ ·) eq
  rw [literal_factor, literal_factor] at e
  have h : projection.map (output .unit .unit (.inl ())) =
      projection.map (output .unit .unit (.inr ())) :=
    congrArg (fun f => projection.map (f ≫ (sumIso (.unit : Ty Empty) .unit).hom)) e
  cases separate_output .unit .unit h

private theorem square :
    step result source sourceRows ≫ coprod.map (𝟙 (obj result.ty)) (branch normalizes.typed.2) =
      branch normalizes.typed.2 ≫ step result target targetRows := by
  apply table_hom_ext source
  intro i
  have left : source.inj i ≫ (step result source sourceRows ≫
        coprod.map (𝟙 (obj result.ty)) (branch normalizes.typed.2)) =
      output result target (.inr (.inl ())) := by
    rw [← Category.assoc, step, inj_table]
    change output result source (.inr i) ≫ _ = _
    have mapped : source.literal i ≫ branch normalizes.typed.2 = target.literal (.inl ()) := by
      rw [← literal_factor, Category.assoc, collapse_row, literal_stable]
    rw [output_inr, output_inr, Category.assoc, coprod.inr_map, ← Category.assoc, mapped]
  rw [left, ← Category.assoc, collapse_row, ← literal_factor, Category.assoc, step, inj_table]
  change output result target (.inr (.inl ())) = literalUnit ≫ output result target (.inr (.inl ()))
  rw [output, ← Category.assoc, literal_stable]

theorem iterate_collapse :
    projection.map (iterate (step result source sourceRows)) =
      projection.map (boundReturn normalizes.typed.1) ≫
        projection.map (iterate (step result target targetRows)) := by
  apply iterate_uniformity result source target normalizes sourceRows (output result target ∘ targetRows)
    (fun _ j _ => ⟨targetRows j, rfl⟩) rfl rfl
  rw [projection.map_comp, projection.map_comp,
    project_update_coprod_map result normalizes, project_update normalizes,
    ← projection.map_comp, ← projection.map_comp, square]
  rfl

end Collapse

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumSquare
