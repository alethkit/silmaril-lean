module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ForwardingTables.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Payloads.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Mixed.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Termination.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms

/-! # Bounded unfolding and cycle cuts with a fixed constructor reset -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTables

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Paper.WithConstructorSequencing ResetTables
open ForwardingTables (obj inj table inj_table hom_ext inj_is_branch)
open UnitSumSquare (Shape Payload StateCode OutputCode)
open UnitSumSquare.Termination (run withInput run_simulates)
open UnitSumSquare.Cycles.Mixed (exists_common_cut forwardingSteps cutTags)
open UnitSumSquare.Cycles.Payloads (run_same_tag cutRows ReachesExit)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {P : τ} {w : Tm Φ} (hw : Tm.BranchValue [] w P)

set_option backward.isDefEq.respectTransparency false

local notation "iterate" => Paper.TypeCategory.iterate

omit [HasTy Φ τ] in
private theorem closed_subst {Γ : VCtx τ} {A : τ} {t : Tm Φ}
    (ht : Tm.BranchValue Γ t A) (emptyCtx : Γ = []) (θ : Nat → Tm Φ) : t.subst θ = t := by
  induction ht with
  | var hi => subst Γ; cases hi
  | unit => rfl
  | pair _ _ ia ib => simp only [Tm.subst, ia, ib]
  | inl _ ih => simp only [Tm.subst, ih]
  | inr _ ih => simp only [Tm.subst, ih]

private theorem branch_comp_eq {Q R S : τ} {a b c : Tm Φ}
    (ha : Tm.BranchValue [Q] a R) (hb : Tm.BranchValue [R] b S)
    (hc : Tm.BranchValue [Q] c S) (e : b.subst (Tm.replaceNewest a) = c) :
    ofRegion (.br (ℓ := 0) rfl ha) ≫ ofRegion (.br (ℓ := 0) rfl hb) = ofRegion (.br (ℓ := 0) rfl hc) := by
  let comp := CfgEta.TypeCategory.seqValueBranches (.br (ℓ := 0) rfl ha) (.br (ℓ := 0) rfl hb)
  rw [ofRegion_comp _ _ comp, ofRegion_eq_iff]
  have liftEq : Tm.singleSubst a ∘ Silmaril.DeBruijn.lift Nat.succ = Tm.replaceNewest a := by
    funext i
    cases i <;> rfl
  simp only [compLSubst, lsubst, liftLSubstVars, substVars_renameVars, Region.substVars, liftEq, e]
  exact Paper.Eqv.refl (.br rfl hc.hasType)

theorem reset_comp_reset {later : Tm Φ} (hlater : Tm.BranchValue [] later P) :
    action hw .literal ≫ action hlater .literal = action hlater .literal :=
  branch_comp_eq (resetValue hw) (resetValue hlater) (resetValue hlater) (closed_subst hlater rfl _)

private theorem reset_idem : action hw .literal ≫ action hw .literal = action hw .literal :=
  reset_comp_reset hw hw

theorem reset_then_inl :
    action hw .literal ≫ (sumCofan P P).inl =
      ofRegion (.br (ℓ := 0) rfl (.inl (B := P) (resetValue hw))) := by
  rw [sumCofan_inl]
  exact branch_comp_eq (resetValue hw) (.inl (.var (i := 0) rfl)) (.inl (resetValue hw)) rfl

theorem reset_then_inr :
    action hw .literal ≫ (sumCofan P P).inr =
      ofRegion (.br (ℓ := 0) rfl (.inr (A := P) (resetValue hw))) := by
  rw [sumCofan_inr]
  exact branch_comp_eq (resetValue hw) (.inr (.var (i := 0) rfl)) (.inr (resetValue hw)) rfl

theorem action_comp (left right : Payload) :
    action hw left ≫ action hw right = action hw (left.then right) := by
  cases left <;> cases right <;> first | exact reset_idem hw | exact Category.id_comp _ | exact Category.comp_id _

private theorem inj_step (A B : Shape) {Y : Paper.TypeCategory (τ := τ) Φ} (exit : B.Row → (ofType P ⟶ Y))
    (p : A.Row → OutputCode B A) (i : A.Row) :
    inj P A i ≫ stepWith hw A exit p = outputWith hw A exit (p i) :=
  inj_table P A _ i

theorem inj_stateMap (A D : Shape) (rows : A.Row → StateCode D) (i : A.Row) :
    inj P A i ≫ stateMap hw A D rows = action hw (rows i).payload ≫ inj P D (rows i).tag :=
  inj_table P A _ i

private theorem iterate_row (A B : Shape) {Y : Paper.TypeCategory (τ := τ) Φ} (exit : B.Row → (ofType P ⟶ Y))
    (p : A.Row → OutputCode B A) (i : A.Row) :
    inj P A i ≫ iterate (stepWith hw A exit p) =
      outputWith hw A exit (p i) ≫ coprod.desc (𝟙 Y) (iterate (stepWith hw A exit p)) := by
  conv_lhs => rw [iterate_fixpoint (stepWith hw A exit p)]
  rw [← Category.assoc, inj_step]

private theorem iterate_run (B A : Shape) {Y : Paper.TypeCategory (τ := τ) Φ} (exit : B.Row → (ofType P ⟶ Y))
    (p : A.Row → OutputCode B A) {n : Nat} {i : A.Row} {o : StateCode B}
    (h : run p n i = some o) :
    inj P A i ≫ iterate (stepWith hw A exit p) = action hw o.payload ≫ exit o.tag := by
  induction n generalizing i o with
  | zero => cases h
  | succ n ih =>
    cases row : p i with
    | mk tag m =>
      cases tag with
      | inl b =>
        have e : (⟨b, m⟩ : StateCode B) = o := Option.some.inj (by simpa only [run, row] using h)
        subst o
        rw [iterate_row, row]
        simp only [outputWith, ForwardingTables.outputWith, Category.assoc, coprod.inl_desc, Category.comp_id]
      | inr j =>
        have e : (run p n j).map (withInput m) = some o := by simpa only [run, row] using h
        obtain ⟨later, hj, rfl⟩ := Option.map_eq_some_iff.mp e
        rw [iterate_row, row]
        simp only [outputWith, ForwardingTables.outputWith, Category.assoc, coprod.inr_desc]
        rw [ih hj, ← Category.assoc, action_comp]
        rfl

private noncomputable def selfStep (Y : Paper.TypeCategory (τ := τ) Φ) (m : Payload) : ofType P ⟶ Y ⨿ ofType P :=
  action hw m ≫ coprod.inr

private theorem self_unfold (Y : Paper.TypeCategory (τ := τ) Φ) (m : Payload) :
    iterate (selfStep hw Y m) = action hw m ≫ iterate (selfStep hw Y m) := by
  conv_lhs => rw [iterate_fixpoint (selfStep hw Y m)]
  rw [selfStep, Category.assoc, coprod.inr_desc]

theorem iterate_selfStep (Y : Paper.TypeCategory (τ := τ) Φ) (m : Payload) :
    iterate (action hw m ≫ (coprod.inr : ofType P ⟶ Y ⨿ ofType P)) = iterate coprod.inr := by
  cases m with
  | forward => rw [action, Category.id_comp]
  | literal =>
    let feedback : ofType P ⟶ Y ⨿ ofType P := coprod.inr
    have square : feedback ≫ coprod.map (𝟙 Y) (action hw .literal) =
        action hw .literal ≫ selfStep hw Y .literal := by
      dsimp only [feedback, selfStep]
      rw [coprod.inr_map, ← Category.assoc, reset_idem]
    have compare := iterate_uniformity_ofBranchValue (resetValue hw) feedback (selfStep hw Y .literal) square
    exact (self_unfold hw Y .literal).trans compare.symm

theorem action_before_self (Y : Paper.TypeCategory (τ := τ) Φ) (m : Payload) :
    action hw m ≫ iterate (coprod.inr : ofType P ⟶ Y ⨿ ofType P) = iterate coprod.inr := by
  calc
    _ = action hw m ≫ iterate (selfStep hw Y m) :=
      congrArg (action hw m ≫ ·) (iterate_selfStep hw Y m).symm
    _ = iterate (selfStep hw Y m) := (self_unfold hw Y m).symm
    _ = _ := iterate_selfStep hw Y m

private theorem iterate_of_cut (B A : Shape) (p : A.Row → OutputCode B A) (mark : A.Row → Bool)
    (out : A.Row → OutputCode B A) (fuel : Nat)
    (computed : ∀ i, run (cutRows p mark) fuel i = some ⟨(out i).tag, (out i).payload⟩) :
    iterate (step hw B A p) = iterate (step hw B A out) := by
  let cut := stepWith hw A (B := .sum B A) (ForwardingTables.output P B A) (cutRows p mark)
  have inner : iterate cut = step hw B A out := hom_ext P A fun i => by
    rw [inj_step]
    exact iterate_run hw (.sum B A) A (ForwardingTables.output P B A) (cutRows p mark) (computed i)
  have collapse : cut ≫ coprod.desc (𝟙 (obj P B ⨿ obj P A)) coprod.inr = step hw B A p := by
    apply hom_ext P A
    intro i
    dsimp only [cut]
    rw [← Category.assoc, inj_step, inj_step]
    cases row : p i with
    | mk tag m =>
      cases tag with
      | inl b => simp [cutRows, cutTags, row, outputWith, ForwardingTables.outputWith, Category.assoc]
      | inr j => cases h : mark i <;>
          simp [cutRows, cutTags, row, h, outputWith, ForwardingTables.outputWith, Category.assoc]
  rw [← collapse, ← iterate_codiagonal, inner]

private theorem iterate_row_recur (B A : Shape) (p : A.Row → OutputCode B A) {i j : A.Row}
    {m : Payload} (e : p i = ⟨.inr j, m⟩) :
    inj P A i ≫ iterate (step hw B A p) = action hw m ≫ (inj P A j ≫ iterate (step hw B A p)) := by
  rw [iterate_row, e]
  simp only [outputWith, ForwardingTables.outputWith, Category.assoc, coprod.inr_desc]

private theorem iterate_row_self (B A : Shape) (p : A.Row → OutputCode B A) (i : A.Row)
    {m : Payload} (e : p i = ⟨.inr i, m⟩) :
    inj P A i ≫ iterate (step hw B A p) =
      iterate (coprod.inr : ofType P ⟶ obj P B ⨿ ofType P) := by
  obtain ⟨a, ha, row⟩ := inj_is_branch (Φ := Φ) P A i
  have square : selfStep hw (obj P B) m ≫ coprod.map (𝟙 (obj P B)) (inj P A i) =
      inj P A i ≫ step hw B A p := by
    rw [inj_step, e, selfStep]
    simp only [outputWith, ForwardingTables.outputWith, Category.assoc, coprod.inr_map]
  rw [row] at square ⊢
  exact (iterate_uniformity_ofBranchValue ha _ _ square).symm.trans (iterate_selfStep hw _ m)

theorem iterate_nonexit_row (B A : Shape) (p : A.Row → OutputCode B A) (i : A.Row)
    (infinite : ¬ ReachesExit p i) :
    inj P A i ≫ iterate (step hw B A p) =
      iterate (coprod.inr : ofType P ⟶ obj P B ⨿ ofType P) := by
  classical
  let tags := fun j => (p j).tag
  obtain ⟨mark, fuel, stops, erased, exits, returns⟩ := exists_common_cut B A tags
  have payload (j : A.Row) : ∃ m, run (cutRows p mark) fuel j = some ⟨stops j, m⟩ :=
    run_same_tag (p := cutRows p mark) (q := forwardingSteps (cutTags tags mark)) (fun _ => rfl) (erased j)
  let out (j : A.Row) : OutputCode B A := ⟨stops j, Classical.choose (payload j)⟩
  rw [iterate_of_cut hw B A p mark out fuel (fun j => Classical.choose_spec (payload j))]
  cases dest : stops i with
  | inl b =>
    obtain ⟨n, o, run⟩ := exits i b dest
    obtain ⟨m, hm⟩ := run_same_tag (p := p) (q := forwardingSteps tags) (fun _ => rfl) run
    exact False.elim (infinite ⟨n, ⟨o.tag, m⟩, hm⟩)
  | inr j =>
    have edge : out i = ⟨.inr j, (out i).payload⟩ :=
      congrArg (fun t => (⟨t, (out i).payload⟩ : OutputCode B A)) dest
    have self : out j = ⟨.inr j, (out j).payload⟩ :=
      congrArg (fun t => (⟨t, (out j).payload⟩ : OutputCode B A)) (returns i j dest).2
    rw [iterate_row_recur hw B A out edge, iterate_row_self hw B A out j self, action_before_self]

theorem iterate_of_codes (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    (square : ∀ i, (p i).mapState rows = (q (rows i).tag).withInput (rows i).payload) :
    iterate (step hw B A p) = stateMap hw A D rows ≫ iterate (step hw B D q) := by
  classical
  apply hom_ext P A
  intro i
  rw [← Category.assoc, inj_stateMap, Category.assoc]
  by_cases exits : ReachesExit p i
  · obtain ⟨n, o, hp⟩ := exits
    have both := (run_simulates B A D rows p q square n i).symm.trans hp
    obtain ⟨target, ht, rfl⟩ := Option.map_eq_some_iff.mp both
    rw [iterate_run hw B A (inj P B) p hp, iterate_run hw B D (inj P B) q ht,
      ← Category.assoc, action_comp]
    rfl
  · have later : ¬ ReachesExit q (rows i).tag := by
      rintro ⟨n, o, h⟩
      have e := run_simulates B A D rows p q square n i
      rw [h, Option.map_some] at e
      exact exits ⟨n, _, e⟩
    rw [iterate_nonexit_row hw B A p i exits, iterate_nonexit_row hw B D q (rows i).tag later,
      action_before_self]

private theorem output_precomp (B A : Shape) (m : Payload) (o : OutputCode B A) :
    action hw m ≫ output hw B A o = output hw B A (o.withInput m) := by
  change action hw m ≫ (action hw o.payload ≫ _) = _
  rw [← Category.assoc, action_comp]
  rfl

private theorem square_left (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (i : A.Row) :
    inj P A i ≫ (step hw B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap hw A D rows)) =
      output hw B D ((p i).mapState rows) := by
  rw [← Category.assoc, inj_step]
  rcases row : p i with ⟨tag, m⟩
  cases tag with
  | inl b => simp [OutputCode.mapState, outputWith, ForwardingTables.outputWith, Category.assoc]
  | inr j =>
    simp only [OutputCode.mapState, outputWith, ForwardingTables.outputWith, Category.assoc, coprod.inr_map]
    rw [← Category.assoc (inj P A j), inj_stateMap]
    simp only [Category.assoc]
    rw [← Category.assoc (action hw m), action_comp]

private theorem square_right (B A D : Shape) (rows : A.Row → StateCode D)
    (q : D.Row → OutputCode B D) (i : A.Row) :
    inj P A i ≫ (stateMap hw A D rows ≫ step hw B D q) =
      output hw B D ((q (rows i).tag).withInput (rows i).payload) := by
  rw [← Category.assoc, inj_stateMap, Category.assoc, inj_step, output_precomp]

theorem square_of_codes (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    (square : ∀ i, (p i).mapState rows = (q (rows i).tag).withInput (rows i).payload) :
    step hw B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap hw A D rows) =
      stateMap hw A D rows ≫ step hw B D q := by
  apply hom_ext P A
  intro i
  rw [square_left, square_right, square]

private theorem equal_tags (sep : SeparatesResetTags hw) (B A : Shape) (x y : OutputCode B A)
    (equal : projection.map (output hw B A x) = projection.map (output hw B A y)) : x.tag = y.tag := by
  classical
  by_contra different
  let left : ofType (Φ := Φ) P ⟶ ofType P ⨿ ofType P := coprod.inl
  let right : ofType (Φ := Φ) P ⟶ ofType P ⨿ ofType P := coprod.inr
  let color (tag : Sum B.Row A.Row) := if tag = x.tag then left else right
  let test := coprod.desc (table P B (color ∘ Sum.inl)) (table P A (color ∘ Sum.inr))
  have observes (z : OutputCode B A) :
      action hw .literal ≫ output hw B A z ≫ test = action hw .literal ≫ color z.tag := by
    rcases z with ⟨tag, m⟩
    have absorbed : action hw .literal ≫ action hw m = action hw .literal := by cases m <;> exact action_comp hw _ _
    cases tag <;>
      simp only [outputWith, ForwardingTables.outputWith, test, Category.assoc, coprod.inl_desc, coprod.inr_desc,
        inj_table, Function.comp_apply] <;> rw [← Category.assoc, absorbed]
  have eq := congrArg (fun f => projection.map (action hw .literal) ≫ f ≫ projection.map test) equal
  rw [← projection.map_comp, ← projection.map_comp, ← projection.map_comp, ← projection.map_comp,
    observes, observes] at eq
  exact sep (by simpa [color, left, right, Ne.symm different] using eq)

private theorem payload_eq (B A : Shape) (x y : OutputCode B A)
    (agree : projection.map (output hw B A x) = projection.map (output hw B A y)) :
    projection.map (action hw x.payload) = projection.map (action hw y.payload) := by
  let untag : obj (Φ := Φ) P B ⨿ obj P A ⟶ ofType P := coprod.desc (table P B fun _ => 𝟙 (ofType P)) (table P A fun _ => 𝟙 (ofType P))
  have cancels (o : OutputCode B A) : output hw B A o ≫ untag = action hw o.payload := by
    rcases o with ⟨tag, m⟩
    cases tag <;> simp only [outputWith, ForwardingTables.outputWith, untag, Category.assoc, coprod.inl_desc,
      coprod.inr_desc, inj_table, Category.comp_id]
  have eq := congrArg (· ≫ projection.map untag) agree
  rw [← projection.map_comp, ← projection.map_comp, cancels, cancels] at eq
  exact eq

theorem separate_output (tags : SeparatesResetTags hw) (modes : SeparatesActions hw) (B A : Shape)
    {x y : OutputCode B A}
    (agree : projection.map (output hw B A x) = projection.map (output hw B A y)) : x = y := by
  have sameTags := equal_tags hw tags B A x y agree
  have samePayload : x.payload = y.payload := by
    have h := payload_eq hw B A x y agree
    cases ex : x.payload <;> cases ey : y.payload <;> rw [ex, ey] at h <;>
      first | exact False.elim (modes h) | exact False.elim (modes h.symm)
  cases x
  cases y
  cases sameTags
  cases samePayload
  rfl

theorem codes_of_projected_square (tags : SeparatesResetTags hw) (modes : SeparatesActions hw)
    (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    (comm : projection.map (step hw B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap hw A D rows)) =
      projection.map (stateMap hw A D rows ≫ step hw B D q)) :
    ∀ i, (p i).mapState rows = (q (rows i).tag).withInput (rows i).payload := by
  intro i
  have e := congrArg (projection.map (inj P A i) ≫ ·) comm
  rw [← projection.map_comp, ← projection.map_comp, square_left, square_right] at e
  exact separate_output hw tags modes B D e

theorem iterate_when_reset_is_id (hId : action hw .literal = 𝟙 (ofType P))
    (B A D : Shape) (rows : A.Row → StateCode D) (p : A.Row → OutputCode B A)
    (q : D.Row → OutputCode B D)
    (payload : ForwardingTables.SeparatesTags (Φ := Φ) P ∨ Nonempty (IsInitial (ofType (Φ := Φ) P)))
    (comm : projection.map (step hw B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap hw A D rows)) =
      projection.map (stateMap hw A D rows ≫ step hw B D q)) :
    iterate (step hw B A p) = stateMap hw A D rows ≫ iterate (step hw B D q) := by
  have trivialAction (m : Payload) : action hw m = 𝟙 (ofType P) := by
    cases m
    · rfl
    · exact hId
  have eraseStep (X : Shape) (r : X.Row → OutputCode B X) :
      step hw B X r = ForwardingTables.step P B X (fun i => (r i).tag) := by
    apply hom_ext P X
    intro i
    rw [inj_step]
    change output hw B X (r i) = inj P X i ≫ table P X (fun j => ForwardingTables.output P B X (r j).tag)
    rw [inj_table]
    simp only [outputWith, trivialAction, Category.id_comp]
  have eraseMap : stateMap hw A D rows = ForwardingTables.stateMap P A D (fun i => (rows i).tag) := by
    apply hom_ext P A
    intro i
    rw [inj_stateMap, ForwardingTables.stateMap, inj_table, trivialAction, Category.id_comp]
    rfl
  rw [eraseStep, eraseStep, eraseMap] at comm ⊢
  exact ForwardingTables.iterate_of_projected_square P B A D _ _ _ payload comm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTables
