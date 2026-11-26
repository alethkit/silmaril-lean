module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.SlotMaps.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Paths.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Pruning.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.ReplaceNewest.Thms

/-! # A written outer cycle with a left-tagged and an ordinary retained row -/

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgMixedSlotsExample

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open UnusedSummand.BlockParameters (Program)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open NestedAdmission (exits)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private inductive Op where
  | poll
  | resume

private abbrev U : Ty Empty := .unit
private abbrev Pair : Ty Empty := .product U U
private abbrev tag (D : Ty Empty) : Ty Empty := .coprod U D
private abbrev innerTypes : Fin 1 → Ty Empty := fun _ => U
private def retainedTypes (first : Ty Empty) : Fin 2 → Ty Empty := Fin.cases first (fun _ => Pair)
private def fullTypes (D dead : Ty Empty) : Fin 3 → Ty Empty := Fin.cases (tag D) (Fin.cases dead (fun _ => Pair))
private abbrev labels (first : Ty Empty) := List.ofFn (retainedTypes first) ++ exits

instance : HasTy Op (Ty Empty) where
  src
    | .poll => U
    | .resume => Pair
  trg
    | .poll => .coprod Pair U
    | .resume => .coprod U Pair

private def inner : Program (Φ := Op) innerTypes (labels U) [U] where
  entry := .jump 0 (.var 0 rfl)
  blocks _ := .parameter (.case (.op Op.poll (.var 0 rfl)) (.exit 1 rfl (.var 0 rfl)) (.exit 2 rfl (.var 0 rfl)))

private def guarded : Region Op :=
  .case (.var 0) (inner.region.renameVars (Silmaril.DeBruijn.lift Nat.succ)) (.br 0 (.var 1))

private def ordinary (wide : Bool) : Region Op :=
  .case (.op .resume (.var 0)) (.br 0 (if wide then .inl (.var 0) else .var 0)) (.br 3 (.var 0))

private def start (wide : Bool) : Region Op := .br 0 (if wide then .inl .unit else .unit)

private def keep : Fin 2 ↪ Fin 3 :=
  ⟨fun i => ⟨2 * i.val, by omega⟩, by
    intro i j h
    have eq := congrArg Fin.val h
    apply Fin.ext
    change 2 * i.val = 2 * j.val at eq
    omega⟩

private def compact : CfgRestriction Op 3 :=
  ⟨start true, Fin.cases guarded (Fin.cases (.br 2 .unit) (Fin.cases (ordinary true) Fin.elim0))⟩

private abbrev graph : Region Op := compact.source keep
private abbrev liveRows : Fin 2 → Region Op := fun i => compact.rows (keep i)
private def commonRows : Fin 2 → Region Op := Fin.cases inner.region (fun _ => ordinary false)

private theorem restrict_ok : CfgRestriction.check? keep exits.length graph = some compact := by
  change some _ = some compact
  apply congrArg some
  unfold compact
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases rfl (fun _ => rfl) j) i
  congr 2
  simp only [Program.region, Region.renameVars]
  congr 1
  funext j
  change Fin 1 at j
  cases Subsingleton.elim j (0 : Fin 1)
  rfl

private def innerKeep : Fin 1 ↪ Fin 1 := Function.Embedding.refl _
private def singleton : Region Op := .cfg (start true) 1 (fun _ => guarded)
private def innerRow : Region Op := (inner.blocks 0).region

private def plan : NestedAdmission.Finite.Plan Op 1 1 :=
  ⟨.unit, U, guarded, inner.entry.region false id, Fin.cases innerRow Fin.elim0,
    inner.entry.region false id, Fin.cases innerRow Fin.elim0⟩

private theorem checkInner : NestedAdmission.Finite.check? innerKeep innerTypes singleton
    (Pair :: exits) = some plan := rfl

private theorem chosen_inner : plan.selectedInner innerKeep = inner.region := by
  unfold NestedAdmission.Finite.Plan.selectedInner Program.region
  congr 1
  funext i
  cases Subsingleton.elim i (0 : Fin 1)
  rfl

private theorem common_inner : plan.commonInner = inner.region := by
  unfold NestedAdmission.Finite.Plan.commonInner Program.region
  congr 1
  funext i
  cases Subsingleton.elim i (0 : Fin 1)
  rfl

private def routeLayout : RouteLayout Empty := (U, true) :: (Pair :: exits).map (fun A => (A, false))
private theorem entryRoute : CheckedRoutes routeLayout [] (start false) (start true) :=
  Region.checkRoutes?_sound rfl
private theorem ordinaryRoute : CheckedRoutes routeLayout [Pair] (ordinary false) (ordinary true) :=
  Region.checkRoutes?_sound rfl

private theorem inner_typed (A : Ty Empty) : inner.region.HasType [U] (labels A) :=
  .cfg innerTypes (.br rfl (.var rfl)) (fun _ =>
    .case (.op (.var rfl)) (.br rfl (.var rfl)) (.br rfl (.var rfl)))

private theorem anchor_plain {S : Fin 2 → Ty Empty} (typed : inner.region.HasType [U] (List.ofFn S ++ exits)) :
    S 1 = Pair :=
  inner.enclosing_type_at_reached (j := 0) (.entry rfl) 1 (Or.inl ⟨rfl, rfl⟩) typed

private theorem anchor_left {S : Fin 2 → Ty Empty}
    (typed : (start true).HasType [] (List.ofFn S ++ exits)) : ∃ D : Ty Empty, S 0 = tag D := by
  have h : At (List.ofFn S ++ exits) 0 (S 0) := by simp [At]
  cases typed with
  | br hit operand =>
      cases operand with
      | inl init => cases init; exact ⟨_, Option.some.inj (h.symm.trans hit)⟩

private theorem actualEntry_typed (D dead : Ty Empty) :
    (compact.entry.renameLabels (retainLabelIndex keep)).HasType [] (List.ofFn (fullTypes D dead) ++ exits) :=
  (show (start true).HasType [] (List.ofFn (fun i => fullTypes D dead (keep i)) ++ exits) from
    .br rfl (.inl .unit)).renameLabels (retainLabelRen keep _ _)

private theorem actualRows_typed (D dead : Ty Empty) (i : Fin 3) :
    ((compact.rows i).renameLabels (retainLabelIndex keep)).HasType
      [fullTypes D dead i] (List.ofFn (fullTypes D dead) ++ exits) := by
  let compactLabels := List.ofFn (fun j => fullTypes D dead (keep j)) ++ exits
  have first : guarded.HasType [tag D] compactLabels :=
    .case (.var rfl) ((inner_typed (tag D)).renameVars ((Ren.wk [] (tag D)).lift U)) (.br rfl (.var rfl))
  have second : (ordinary true).HasType [Pair] compactLabels :=
    .case (.op (.var rfl)) (.br rfl (.inl (.var rfl))) (.br rfl (.var rfl))
  have omitted : (Region.br 2 .unit : Region Op).HasType [dead] compactLabels := .br rfl .unit
  have ren := retainLabelRen keep (fullTypes D dead) exits
  exact Fin.cases (first.renameLabels ren)
    (Fin.cases (omitted.renameLabels ren) (Fin.cases (second.renameLabels ren) (fun j => Fin.elim0 j))) i

private def replies (exitPair : Bool) : Op → Value Empty → Nat → Value Empty → Nat → Prop
  | .poll, .unit, 0, .inl (.pair .unit .unit), 1 => True
  | .resume, .pair .unit .unit, 1, .inl .unit, 2 => exitPair = false
  | .resume, .pair .unit .unit, 1, .inr (.pair .unit .unit), 2 => exitPair = true
  | .poll, .unit, 2, .inr .unit, 3 => True
  | _, _, _, _, _ => False

/-- The nested request transfers to outer slot two, whose request sends a
tagged reply back to slot zero. The next nested request takes exit zero. -/
example : Semantics.Region.Eval (replies false) (fun _ => .unit) graph 0 0 .unit 3 := by
  refine .cfg (.br (.inl .unit)) ?_
  refine .step (label := 0) (next := 2) (middle := .pair .unit .unit) (s₁ := 1) (by decide) ?_ ?_
  · exact .case_inl .var (.cfg (.br .var)
      (.step (label := 0) (next := 3) (by decide)
        (.case_inl (.op .var
          (show replies false Op.poll .unit 0 (.inl (.pair .unit .unit)) 1 from True.intro)) (.br .var))
        (.exit (by decide))))
  · refine .step (label := 2) (next := 0) (middle := .inl .unit) (s₁ := 2) (by decide)
      (.case_inl (.op .var rfl) (.br (.inl .var))) ?_
    refine .step (label := 0) (next := 3) (middle := .unit) (s₁ := 3) (by decide) ?_ (.exit (by decide))
    exact .case_inl .var (.cfg (.br .var)
      (.step (label := 0) (next := 4) (by decide)
        (.case_inr (.op .var
          (show replies false Op.poll .unit 2 (.inr .unit) 3 from True.intro)) (.br .var))
        (.exit (by decide))))

/-- Another reply from the ordinary row reaches the distinct pair exit. -/
example : Semantics.Region.Eval (replies true) (fun _ => .unit) graph 0 1 (.pair .unit .unit) 2 := by
  refine .cfg (.br (.inl .unit)) ?_
  refine .step (label := 0) (next := 2) (middle := .pair .unit .unit) (s₁ := 1) (by decide) ?_ ?_
  · exact .case_inl .var (.cfg (.br .var)
      (.step (label := 0) (next := 3) (by decide)
        (.case_inl (.op .var
          (show replies true Op.poll .unit 0 (.inl (.pair .unit .unit)) 1 from True.intro)) (.br .var))
        (.exit (by decide))))
  · exact .step (label := 2) (next := 4) (by decide)
      (.case_inr (.op .var rfl) (.br .var)) (.exit (by decide))

section ValueMaps

variable {V : Type} [Category V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel (Ty Empty) V)

private noncomputable abbrev leftIn (D : Ty Empty) : M.obj U ⟶ M.obj (tag D) :=
  coprod.inl ≫ (M.coprodIso U D).inv

private noncomputable def slot (D : Ty Empty) (i : Fin 2) :
    M.obj (retainedTypes U i) ⟶ M.obj (retainedTypes (tag D) i) :=
  Fin.cases (leftIn M D) (fun _ => 𝟙 (M.obj Pair)) i

private noncomputable abbrev post (D : Ty Empty) := mapLabelHead M (Pair :: exits) (leftIn M D)
private noncomputable abbrev cut (A : Ty Empty) := labelAppendSplit M (List.ofFn (retainedTypes A)) exits
private noncomputable abbrev stepPost (D : Ty Empty) :=
  coprod.map (𝟙 (labelObj M exits)) (mapSlotLabels M (slot M D))

@[reassoc] private theorem cut_zero (A : Ty Empty) :
    labelInject M 0 (rfl : At (labels A) 0 A) ≫ cut M A =
      labelInject M 0 (rfl : At (List.ofFn (retainedTypes A)) 0 A) ≫ coprod.inr :=
  labelAppendSplit_local M (retainedTypes A) exits 0 rfl rfl

@[reassoc] private theorem cut_one (A : Ty Empty) :
    labelInject M 1 (rfl : At (labels A) 1 Pair) ≫ cut M A =
      labelInject M 1 (rfl : At (List.ofFn (retainedTypes A)) 1 Pair) ≫ coprod.inr :=
  labelAppendSplit_local M (retainedTypes A) exits 1 rfl rfl

@[reassoc] private theorem cut_exit (A : Ty Empty) {i : Nat} {T : Ty Empty} (h : At exits i T) :
    labelInject M (i + 2) (show At (labels A) (i + 2) T from h) ≫ cut M A =
      labelInject M i h ≫ coprod.inl := by
  have shifted : At (labels A) (i + 2) T := h
  have exit := labelAppendSplit_exit M (retainedTypes A) exits h (by simpa only [Nat.add_comm 2 i] using shifted)
  simpa only [Nat.add_comm 2 i] using exit

private theorem post_cut (D : Ty Empty) : post M D ≫ cut M (tag D) = cut M U ≫ stepPost M D := by
  apply labelHom_ext M
  intro i A hit
  cases i with
  | zero =>
      have eq : U = A := Option.some.inj hit
      subst A
      simp only [post, mapLabelHead_zero_assoc, cut_zero, cut_zero_assoc, stepPost, coprod.inr_map]
      exact (mapSlotLabels_inject_assoc M (slot M D) (0 : Fin 2) rfl rfl coprod.inr).symm
  | succ i =>
      cases i with
      | zero =>
          have eq : Pair = A := Option.some.inj hit
          subst A
          rw [mapLabelHead_succ_assoc M (Pair :: exits) (leftIn M D) (i := 0) rfl]
          change labelInject M 1 (rfl : At (labels (tag D)) 1 Pair) ≫ cut M (tag D) =
            labelInject M 1 (rfl : At (labels U) 1 Pair) ≫ cut M U ≫ stepPost M D
          simp only [cut_one, cut_one_assoc, stepPost, coprod.inr_map]
          have eq := mapSlotLabels_inject_assoc M (slot M D) (1 : Fin 2) rfl rfl
            (coprod.inr : labelObj M (List.ofFn (retainedTypes (tag D))) ⟶ labelObj M exits ⨿ _)
          have identity : slot M D (1 : Fin 2) = 𝟙 (M.obj Pair) := rfl
          rw [identity] at eq
          exact (Category.id_comp _).symm.trans eq.symm
      | succ i =>
          have hi : At exits i A := hit
          have tail : At (Pair :: exits) (i + 1) A := hi
          simp only [post, mapLabelHead_succ_assoc M (Pair :: exits) (leftIn M D) tail,
            cut_exit M _ hi, cut_exit_assoc M _ hi, stepPost, coprod.inl_map, Category.id_comp]

private theorem checked_routes (D : Ty Empty) {Γ : VCtx (Ty Empty)} {r s : Region Op}
    (checked : CheckedRoutes routeLayout Γ r s) : RegionConstructorRoutes M (post M D) (𝟙 _) Γ r s := by
  apply CheckedRoutes.toConstructorRoutes M checked
  · intro i A hit
    cases i with
    | zero => simp [routeLayout] at hit
    | succ i =>
        simp only [routeLayout, List.getElem?_cons_succ, List.getElem?_map] at hit
        obtain ⟨T, get, eq⟩ := Option.map_eq_some_iff.mp hit
        have ht : At (Pair :: exits) i A := get.trans (congrArg (fun x : Ty Empty × Bool => some x.1) eq)
        exact ⟨ht, ht, (mapLabelHead_succ M (Pair :: exits) (leftIn M D) ht).trans (Category.comp_id _).symm⟩
  · intro i A hit
    cases i with
    | zero =>
        have eq : U = A := congrArg Prod.fst (Option.some.inj hit)
        subst A
        exact ⟨D, rfl, rfl, by rw [Category.comp_id]; exact mapLabelHead_zero M (Pair :: exits) (leftIn M D)⟩
    | succ i =>
        simp only [routeLayout, List.getElem?_cons_succ, List.getElem?_map] at hit
        obtain ⟨_, _, eq⟩ := Option.map_eq_some_iff.mp hit
        cases eq

private theorem append_cut {C : Type} [Category C] (J : V ⥤ C) {D : Ty Empty}
    {Γ : VCtx (Ty Empty)} {a : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (labels U))}
    {b : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (labels (tag D)))}
    (eq : b = a ≫ J.map (post M D)) :
    b ≫ J.map (cut M (tag D)) = a ≫ J.map (cut M U) ≫ J.map (stepPost M D) := by
  rw [eq, Category.assoc, ← J.map_comp, post_cut, J.map_comp]

end ValueMaps

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

local notation "Env" => ctxObj M []
local notation "Arrow" => J.obj Env ⟶ J.obj (labelObj M exits)

private theorem select_inner (D : Ty Empty) {L : LCtx (Ty Empty)} {t : guarded.HasType [tag D] L}
    {b : J.obj (ctxObj M [tag D]) ⟶ J.obj (labelObj M L)} (w : RegionDenotes J M t b) :
    ∃ h : inner.region.HasType [U] L, RegionDenotes J M h (J.map (Env ◁ leftIn M D) ≫ b) := by
  have da : Denotes J M (.inl (.var rfl) (B := D) : (Tm.inl (.var 0) : Tm Op).HasType [U] (tag D))
      (J.map (snd Env (M.obj U) ≫ leftIn M D)) := by
    rw [J.map_comp]
    exact .inl (.var rfl)
  obtain ⟨_, restricted⟩ := w.replaceNewest J M da
  have prune : Region.PruneConstructorTests (guarded.substVars (Tm.replaceNewest (.inl (.var 0))))
      (plan.selectedInner innerKeep) := (NestedAdmission.Finite.check?_sound checkInner).outer
  rw [chosen_inner] at prune
  exact prune.denotes J M restricted

private theorem align {S : Fin 2 → Ty Empty} {f : Arrow}
    (w : CfgDenotesAt J M S compact.entry liveRows f) : ∃ D : Ty Empty, S = retainedTypes (tag D) := by
  obtain ⟨ent, _, _, b, _, _, rows, _⟩ := w
  obtain ⟨D, first⟩ := anchor_left ent
  have row : ∃ (t : guarded.HasType [tag D] (List.ofFn S ++ exits))
      (a : J.obj (ctxObj M [tag D]) ⟶ J.obj (labelObj M (List.ofFn S ++ exits))), RegionDenotes J M t a := by
    rw [← first]
    exact ⟨_, b 0, rows 0⟩
  obtain ⟨_, _, row⟩ := row
  obtain ⟨selected, _⟩ := select_inner J M D row
  have second := anchor_plain selected
  refine ⟨D, funext (Fin.cases first ?_)⟩
  intro i
  cases Subsingleton.elim i (0 : Fin 1)
  exact second

private theorem compare_reduced (roll : IterationRolling C) (D : Ty Empty) {f g : Arrow}
    (small : CfgDenotesAt J M (retainedTypes U) (start false) commonRows f)
    (wide : CfgDenotesAt J M (retainedTypes (tag D)) compact.entry liveRows g) : f = g := by
  have mapped := CfgDenotesAt.postmap_of_slot_squares J M (slot M D) (𝟙 (labelObj M exits))
    (fun _ _ _ _ de dw => by
      have eq := RegionConstructorRoutes.denotes J M (checked_routes M D entryRoute) de dw
      rw [J.map_id, Category.comp_id] at eq
      exact append_cut M J eq.symm)
    (fun i => Fin.cases (fun _ _ a b ds dw => by
      obtain ⟨_, selected⟩ := select_inner J M D dw
      obtain ⟨_, common⟩ : ∃ t : plan.commonInner.HasType [U] (labels U), RegionDenotes J M t a := by
        rw [common_inner]
        exact ⟨_, ds⟩
      obtain ⟨_, wide⟩ : ∃ t : (plan.selectedInner innerKeep).HasType [U] (labels (tag D)),
          RegionDenotes J M t (J.map (Env ◁ leftIn M D) ≫ b) := by
        rw [chosen_inner]
        exact ⟨_, selected⟩
      have eq := (NestedAdmission.Finite.check?_sound checkInner).postmap_inner J M roll D common wide
      have component := append_cut M J eq
      rw [Category.assoc] at component
      exact component)
      (fun j => by
        cases Subsingleton.elim j (0 : Fin 1)
        intro _ _ _ _ ds dw
        have eq := RegionConstructorRoutes.denotes J M (checked_routes M D ordinaryRoute) ds dw
        rw [J.map_id, Category.comp_id] at eq
        change J.map (Env ◁ 𝟙 (M.obj Pair)) ≫ _ ≫ _ = _
        rw [MonoidalCategory.whiskerLeft_id, J.map_id, Category.id_comp]
        exact append_cut M J eq.symm) i)
    small wide
  rwa [J.map_id, Category.comp_id, eq_comm] at mapped

private theorem compare_original (roll : IterationRolling C)
    {h h' : graph.HasType [] exits} {f g : Arrow}
    (left : RegionDenotes J M h f) (right : RegionDenotes J M h' g) : f = g := by
  have rows : ∀ i, (commonRows i).HasType [retainedTypes U i] (labels U) :=
    Fin.cases (inner_typed U) (fun _ => ordinaryRoute.hasType)
  obtain ⟨base, small⟩ := CfgDenotesAt.exists_of_typing J M (retainedTypes U) (L := exits)
    entryRoute.hasType rows
  have agree {ht : graph.HasType [] exits} {a : Arrow} (actual : RegionDenotes J M ht a) : base = a := by
    obtain ⟨_, _, reduced⟩ := (CfgRestriction.check?_sound restrict_ok).readback J M roll actual
    obtain ⟨D, shape⟩ := align J M reduced
    rw [shape] at reduced
    exact compare_reduced J M roll D small reduced
  exact (agree left).symm.trans (agree right)

/-- Compare independently typed denotations of the same original full
graph. Both the unused right summand and the omitted outer slot vary. -/
example (roll : IterationRolling C) :
    ∃ f g : Arrow,
      CfgDenotesAt J M (fullTypes U U) (compact.entry.renameLabels (retainLabelIndex keep))
        (fun i => (compact.rows i).renameLabels (retainLabelIndex keep)) f ∧
      CfgDenotesAt J M (fullTypes .empty .empty) (compact.entry.renameLabels (retainLabelIndex keep))
        (fun i => (compact.rows i).renameLabels (retainLabelIndex keep)) g ∧ f = g := by
  obtain ⟨f, left⟩ := CfgDenotesAt.exists_of_typing J M (fullTypes U U) (actualEntry_typed U U) (actualRows_typed U U)
  obtain ⟨g, right⟩ := CfgDenotesAt.exists_of_typing J M (fullTypes .empty .empty)
    (actualEntry_typed .empty .empty) (actualRows_typed .empty .empty)
  have tl : graph.HasType [] exits := .cfg (fullTypes U U) (actualEntry_typed U U) (actualRows_typed U U)
  have tr : graph.HasType [] exits := .cfg (fullTypes .empty .empty)
    (actualEntry_typed .empty .empty) (actualRows_typed .empty .empty)
  have dl : RegionDenotes J M tl f := left.denotes J M
  have dr : RegionDenotes J M tr g := right.denotes J M
  exact ⟨f, g, left, right, compare_original J M roll dl dr⟩

end Model

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgMixedSlotsExample
