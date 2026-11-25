module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ForwardingTables.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Mixed.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Termination.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms

/-! # Row reconstruction and finite iteration of forwarding tables -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTables

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Paper.WithConstructorSequencing ForwardingTables
open UnitSumSquare (Shape StateCode OutputCode)
open UnitSumSquare.Cycles.Mixed (cutTags forwardingSteps exists_common_cut)
open UnitSumSquare.Termination (run forwardingRows run_simulates)
open scoped Paper.BoundSimulation.Obstruction

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option backward.isDefEq.respectTransparency false

theorem inj_table (P : τ) (A : Shape) {X : Paper.TypeCategory (τ := τ) Φ}
    (rows : A.Row → (ofType P ⟶ X)) (i : A.Row) : inj P A i ≫ table P A rows = rows i := by
  induction A with
  | empty => exact i.elim
  | unit => cases i; exact Category.id_comp _
  | sum A B ihA ihB =>
    cases i with
    | inl i =>
      rw [inj, table, Category.assoc, ← Category.assoc (sumCofan (sumType P A) (sumType P B)).inl,
        sumCofan_inl_sumIso_hom, coprod.inl_desc]
      exact ihA _ i
    | inr i =>
      rw [inj, table, Category.assoc, ← Category.assoc (sumCofan (sumType P A) (sumType P B)).inr,
        sumCofan_inr_sumIso_hom, coprod.inr_desc]
      exact ihB _ i

theorem hom_ext (P : τ) (A : Shape) {X : Paper.TypeCategory (τ := τ) Φ} {f g : obj P A ⟶ X}
    (h : ∀ i, inj P A i ≫ f = inj P A i ≫ g) : f = g := by
  induction A with
  | empty => exact emptyHom_ext f g
  | unit => simpa only [inj, Category.id_comp] using h ()
  | sum A B ihA ihB =>
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit (sumType P A) (sumType P B))
    · exact ihA fun i => by simpa only [inj, Category.assoc] using h (.inl i)
    · exact ihB fun i => by simpa only [inj, Category.assoc] using h (.inr i)

/-- Composition of a single guarded branch with a constructor tag stays a single branch. -/
private theorem branch_comp {P Q R : τ} {a b : Tm Φ}
    (ha : Tm.BranchValue [P] a Q) (hb : Tm.BranchValue [Q] b R) :
    ∃ (c : Tm Φ) (hc : Tm.BranchValue [P] c R),
      ofRegion (.br (ℓ := 0) rfl ha) ≫ ofRegion (.br (ℓ := 0) rfl hb) =
        ofRegion (.br (ℓ := 0) rfl hc) := by
  let θ := Tm.consSubst a (Tm.var ∘ Nat.succ)
  have ty : ∀ ⦃i : Nat⦄ ⦃X : τ⦄, At [Q] i X → Tm.BranchValue [P] (θ i) X := by
    intro i X hi
    cases i with
    | zero => cases Option.some.inj hi; exact ha
    | succ i => cases i <;> contradiction
  let hr := CfgEta.TypeCategory.seqValueBranches (.br (ℓ := 0) rfl ha) (.br (ℓ := 0) rfl hb)
  refine ⟨b.subst θ, hb.subst ty, ?_⟩
  rw [ofRegion_comp _ _ hr, ofRegion_eq_iff]
  have hz : Tm.singleSubst a ∘ Silmaril.DeBruijn.lift Nat.succ = θ := by
    funext i
    cases i <;> rfl
  simp only [compLSubst, lsubst, liftLSubstVars, substVars_renameVars, hz, Region.substVars]
  exact Paper.Eqv.refl (.br rfl (hb.subst ty).hasType)

theorem inj_is_branch (P : τ) (A : Shape) (i : A.Row) :
    ∃ (a : Tm Φ) (ha : Tm.BranchValue [P] a (sumType P A)),
      inj P A i = ofRegion (.br (ℓ := 0) rfl ha) := by
  induction A with
  | empty => exact i.elim
  | unit => exact ⟨.var 0, .var (i := 0) rfl, (ofRegion_id P).symm⟩
  | sum A B ihA ihB =>
    cases i with
    | inl i =>
      obtain ⟨a, ha, e⟩ := ihA i
      simpa only [inj, e, sumType, sumCofan_inl] using
        branch_comp ha (.inl (B := sumType P B) (.var (i := 0) rfl))
    | inr i =>
      obtain ⟨a, ha, e⟩ := ihB i
      simpa only [inj, e, sumType, sumCofan_inr] using
        branch_comp ha (.inr (A := sumType P A) (.var (i := 0) rfl))

theorem separate_output (P : τ) (hP : SeparatesTags (Φ := Φ) P) (B A : Shape)
    {x y : Sum B.Row A.Row} (h : projection.map (output (Φ := Φ) P B A x) =
      projection.map (output (Φ := Φ) P B A y)) : x = y := by
  classical
  by_contra different
  let left : ofType (Φ := Φ) P ⟶ ofType P ⨿ ofType P := coprod.inl
  let right : ofType (Φ := Φ) P ⟶ ofType P ⨿ ofType P := coprod.inr
  let color (z : Sum B.Row A.Row) := if z = x then left else right
  let test := coprod.desc (table P B (color ∘ Sum.inl)) (table P A (color ∘ Sum.inr))
  have observes (z : Sum B.Row A.Row) : output P B A z ≫ test = color z := by
    cases z <;> simp only [outputWith, test, Category.assoc, coprod.inl_desc, coprod.inr_desc, inj_table,
      Function.comp_apply]
  have e := congrArg (· ≫ projection.map test) h
  rw [← projection.map_comp, ← projection.map_comp, observes, observes] at e
  exact hP (by simpa [color, left, right, Ne.symm different] using e)

private theorem step_post_state (P : τ) (B A D : Shape) (tags : A.Row → D.Row)
    (z : Sum B.Row A.Row) :
    output (Φ := Φ) P B A z ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D tags) =
      output P B D (z.map id tags) := by
  cases z with
  | inl b => simp [outputWith, Category.assoc]
  | inr j =>
    simp only [outputWith, Category.assoc, coprod.inr_map]
    rw [← Category.assoc, stateMap, inj_table]
    rfl

private theorem square_left (P : τ) (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (i : A.Row) :
    inj (Φ := Φ) P A i ≫ (step P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D tags)) =
      output P B D ((p i).map id tags) := by
  rw [← Category.assoc]
  change (inj P A i ≫ table P A (output P B A ∘ p)) ≫ _ = _
  rw [inj_table]
  exact step_post_state P B A D tags (p i)

private theorem square_right (P : τ) (B A D : Shape) (tags : A.Row → D.Row)
    (q : D.Row → Sum B.Row D.Row) (i : A.Row) :
    inj (Φ := Φ) P A i ≫ (stateMap P A D tags ≫ step P B D q) = output P B D (q (tags i)) := by
  rw [← Category.assoc, stateMap, inj_table]
  exact inj_table P D _ (tags i)

theorem square_of_tags (P : τ) (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (comm : ∀ i, (p i).map id tags = q (tags i)) :
    step (Φ := Φ) P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D tags) =
      stateMap P A D tags ≫ step P B D q := by
  apply hom_ext P A
  intro i
  rw [square_left, square_right, comm]

theorem tags_of_projected_square (P : τ) (hP : SeparatesTags (Φ := Φ) P)
    (B A D : Shape) (tags : A.Row → D.Row) (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (comm : projection.map (step (Φ := Φ) P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D tags)) =
      projection.map (stateMap P A D tags ≫ step P B D q)) :
    ∀ i, (p i).map id tags = q (tags i) := by
  intro i
  have e := congrArg (projection.map (inj P A i) ≫ ·) comm
  rw [← projection.map_comp, ← projection.map_comp, square_left, square_right] at e
  exact separate_output P hP B D e

private theorem map_forward {B : Shape} (o : Option (StateCode B)) :
    o.map (UnitSumSquare.Termination.withInput .forward) = o := by
  cases o with
  | none => rfl
  | some o => rcases o with ⟨tag, p⟩; cases p <;> rfl

private theorem run_succ {B A : Shape} (p : A.Row → Sum B.Row A.Row) (n : Nat) (i : A.Row) :
    run (forwardingSteps p) (n + 1) i = match p i with
      | .inl b => some ⟨b, .forward⟩
      | .inr j => run (forwardingSteps p) n j := by
  cases h : p i <;> simp [run, forwardingSteps, h, map_forward]

private theorem iterate_run (P : τ) (B A : Shape) {Y : Paper.TypeCategory (τ := τ) Φ}
    (exit : B.Row → (ofType P ⟶ Y)) (p : A.Row → Sum B.Row A.Row)
    {n : Nat} {i : A.Row} {o : StateCode B} (h : run (forwardingSteps p) n i = some o) :
    inj P A i ≫ iterate (stepWith P A exit p) = exit o.tag := by
  induction n generalizing i with
  | zero => cases h
  | succ n ih =>
    have unfold : inj P A i ≫ iterate (stepWith P A exit p) =
        outputWith P A exit (p i) ≫ coprod.desc (𝟙 Y) (iterate (stepWith P A exit p)) := by
      conv_lhs => rw [iterate_fixpoint (stepWith P A exit p)]
      rw [← Category.assoc, stepWith, inj_table]
      rfl
    cases row : p i with
    | inl b =>
      have e : (⟨b, .forward⟩ : StateCode B) = o := Option.some.inj (by simpa [run_succ, row] using h)
      rw [unfold, row, outputWith, Category.assoc, coprod.inl_desc, Category.comp_id, ← e]
    | inr j =>
      rw [unfold, row, outputWith, Category.assoc, coprod.inr_desc]
      exact ih (by simpa [run_succ, row] using h)

private theorem iterate_of_cut (P : τ) (B A : Shape) (p : A.Row → Sum B.Row A.Row)
    (mark : A.Row → Bool) (out : A.Row → Sum B.Row A.Row) (fuel : Nat)
    (computed : ∀ i, run (forwardingSteps (cutTags p mark)) fuel i = some ⟨out i, .forward⟩) :
    iterate (step (Φ := Φ) P B A p) = iterate (step P B A out) := by
  let cut := stepWith P A (output (Φ := Φ) P B A) (cutTags p mark)
  have inner : iterate cut = step P B A out := hom_ext P A fun i =>
    (iterate_run P (.sum B A) A (output P B A) (cutTags p mark) (computed i)).trans
      (inj_table P A (output P B A ∘ out) i).symm
  have collapse : cut ≫ coprod.desc (𝟙 (obj P B ⨿ obj P A)) coprod.inr = step P B A p := by
    apply hom_ext P A
    intro i
    simp only [cut, ← Category.assoc, stepWith, inj_table, Function.comp_apply]
    cases e : p i with
    | inl b => simp [cutTags, e, outputWith, Category.assoc]
    | inr j => cases h : mark i <;> simp [cutTags, e, h, outputWith, Category.assoc]
  rw [← collapse, ← iterate_codiagonal, inner]

private theorem iterate_row_recur (P : τ) (B A : Shape) (p : A.Row → Sum B.Row A.Row)
    {i j : A.Row} (e : p i = .inr j) :
    inj (Φ := Φ) P A i ≫ iterate (step P B A p) = inj P A j ≫ iterate (step P B A p) := by
  conv_lhs => rw [iterate_fixpoint (step P B A p)]
  rw [← Category.assoc]
  change (inj P A i ≫ table P A (output P B A ∘ p)) ≫ _ = _
  rw [inj_table]
  change output P B A (p i) ≫ _ = _
  simp [e, outputWith, Category.assoc]

private theorem iterate_row_self (P : τ) (B A : Shape) (p : A.Row → Sum B.Row A.Row)
    (i : A.Row) (e : p i = .inr i) :
    inj (Φ := Φ) P A i ≫ iterate (step P B A p) =
      iterate (coprod.inr : ofType P ⟶ obj P B ⨿ ofType P) := by
  obtain ⟨a, ha, row⟩ := inj_is_branch (Φ := Φ) P A i
  have square : (coprod.inr : ofType (Φ := Φ) P ⟶ obj P B ⨿ ofType P) ≫
      coprod.map (𝟙 (obj P B)) (inj P A i) = inj P A i ≫ step P B A p := by
    rw [coprod.inr_map]
    change _ = inj P A i ≫ table P A (output P B A ∘ p)
    rw [inj_table]
    exact congrArg (output P B A) e.symm
  rw [row] at square ⊢
  exact (iterate_uniformity_ofBranchValue ha _ _ square).symm

theorem iterate_nonexit_row (P : τ) (B A : Shape) (p : A.Row → Sum B.Row A.Row) (i : A.Row)
    (infinite : ¬ UnitSumSquare.Cycles.Mixed.ReachesExit p i) :
    inj (Φ := Φ) P A i ≫ iterate (step P B A p) =
      iterate (coprod.inr : ofType P ⟶ obj P B ⨿ ofType P) := by
  obtain ⟨mark, fuel, out, computed, exits, returns⟩ := exists_common_cut B A p
  rw [iterate_of_cut P B A p mark out fuel computed]
  cases code : out i with
  | inl b => exact False.elim (infinite (exits i b code))
  | inr j =>
    exact (iterate_row_recur P B A out code).trans (iterate_row_self P B A out j (returns i j code).2)

private theorem runs_simulate (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (comm : ∀ i, (p i).map id tags = q (tags i)) (n : Nat) (i : A.Row) :
    run (forwardingSteps p) n i = run (forwardingSteps q) n (tags i) := by
  have square (j : A.Row) : (forwardingSteps p j).mapState (forwardingRows tags) =
      (forwardingSteps q (tags j)).withInput .forward := by
    have h := comm j
    cases e : p j <;> simp [e] at h
    all_goals
      simp only [forwardingSteps]
      rw [← h]
      simp only [forwardingRows, e, OutputCode.mapState, OutputCode.withInput, UnitSumSquare.Payload.then]
  simpa only [forwardingRows, map_forward] using
    run_simulates B A D (forwardingRows tags) (forwardingSteps p) (forwardingSteps q) square n i

theorem iterate_of_tags (P : τ) (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (comm : ∀ i, (p i).map id tags = q (tags i)) :
    iterate (step (Φ := Φ) P B A p) = stateMap P A D tags ≫ iterate (step P B D q) := by
  classical
  apply hom_ext P A
  intro i
  rw [← Category.assoc, stateMap, inj_table]
  change inj P A i ≫ iterate (step P B A p) = inj P D (tags i) ≫ iterate (step P B D q)
  by_cases h : UnitSumSquare.Cycles.Mixed.ReachesExit p i
  · obtain ⟨n, o, hp⟩ := h
    have hq := (runs_simulate B A D tags p q comm n i).symm.trans hp
    exact (iterate_run P B A (inj P B) p hp).trans (iterate_run P B D (inj P B) q hq).symm
  · have later : ¬ UnitSumSquare.Cycles.Mixed.ReachesExit q (tags i) :=
      fun ⟨n, o, hq⟩ => h ⟨n, o, (runs_simulate B A D tags p q comm n i).trans hq⟩
    rw [iterate_nonexit_row P B A p i h, iterate_nonexit_row P B D q (tags i) later]

theorem iterate_of_projected_square (P : τ) (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (payload : SeparatesTags (Φ := Φ) P ∨ Nonempty (IsInitial (ofType (Φ := Φ) P)))
    (comm : projection.map (step (Φ := Φ) P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D tags)) =
      projection.map (stateMap P A D tags ≫ step P B D q)) :
    iterate (step (Φ := Φ) P B A p) = stateMap P A D tags ≫ iterate (step P B D q) := by
  rcases payload with separate | ⟨initial⟩
  · exact iterate_of_tags P B A D tags p q (tags_of_projected_square P separate B A D tags p q comm)
  · cases initial with
    | intro h => exact hom_ext P A fun _ => IsInitial.hom_ext h _ _

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTables
