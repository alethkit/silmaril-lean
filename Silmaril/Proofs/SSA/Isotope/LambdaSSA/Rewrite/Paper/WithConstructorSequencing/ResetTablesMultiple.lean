module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Multiple.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Thms
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.ResetTablesMultipleControl

/-! # Iteration with varying closed constructor assignments -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultiple

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Paper.WithConstructorSequencing ResetTables.Multiple
open ForwardingTables (obj inj table inj_table hom_ext inj_is_branch)
open UnitSumSquare (Shape)
open UnitSumSquare.Cycles.Mixed (cutTags)
open ResetTablesMultipleControl (exists_summary run_simulates)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] (P : τ)

local notation "Mode" => Option (ClosedValue Φ P)
local notation "iterate" => Paper.TypeCategory.iterate

set_option backward.isDefEq.respectTransparency false

theorem action_comp (before after : Mode) :
    action P before ≫ action P after = action P (thenReset before after) := by
  cases before with
  | none =>
    cases after <;> exact Category.id_comp _
  | some earlier =>
    cases after with
    | none => exact Category.comp_id _
    | some later => exact ResetTables.reset_comp_reset earlier.property later.property

private theorem inj_step (A B : Shape) {Y : Paper.TypeCategory (τ := τ) Φ} (exit : B.Row → (ofType P ⟶ Y))
    (p : A.Row → OutputCode (ClosedValue Φ P) B A) (i : A.Row) :
    inj P A i ≫ stepWith P A exit p = outputWith P A exit (p i) :=
  inj_table P A _ i

theorem inj_stateMap (A D : Shape) (rows : A.Row → StateCode (ClosedValue Φ P) D) (i : A.Row) :
    inj P A i ≫ stateMap P A D rows = action P (rows i).reset ≫ inj P D (rows i).tag :=
  inj_table P A _ i

private theorem iterate_row (A B : Shape) {Y : Paper.TypeCategory (τ := τ) Φ} (exit : B.Row → (ofType P ⟶ Y))
    (p : A.Row → OutputCode (ClosedValue Φ P) B A) (i : A.Row) :
    inj P A i ≫ iterate (stepWith P A exit p) =
      outputWith P A exit (p i) ≫ coprod.desc (𝟙 Y) (iterate (stepWith P A exit p)) := by
  conv_lhs => rw [iterate_fixpoint (stepWith P A exit p)]
  rw [← Category.assoc, inj_step]

theorem iterate_runWith (B A : Shape) {Y : Paper.TypeCategory (τ := τ) Φ} (exit : B.Row → (ofType P ⟶ Y))
    (p : A.Row → OutputCode (ClosedValue Φ P) B A) {n : Nat} {i : A.Row} {o : StateCode (ClosedValue Φ P) B}
    (h : run p n i = some o) :
    inj P A i ≫ iterate (stepWith P A exit p) = action P o.reset ≫ exit o.tag := by
  induction n generalizing i o with
  | zero => cases h
  | succ n ih =>
    cases row : p i with
    | mk tag m =>
      cases tag with
      | inl b =>
        have e : (⟨b, m⟩ : StateCode (ClosedValue Φ P) B) = o := Option.some.inj (by simpa only [run, row] using h)
        subst o
        rw [iterate_row, row]
        simp only [outputWith, ForwardingTables.outputWith, Category.assoc, coprod.inl_desc, Category.comp_id]
      | inr j =>
        have e : (run p n j).map (fun out => out.withInput m) = some o := by simpa only [run, row] using h
        obtain ⟨later, hj, rfl⟩ := Option.map_eq_some_iff.mp e
        rw [iterate_row, row]
        simp only [outputWith, ForwardingTables.outputWith, Category.assoc, coprod.inr_desc]
        rw [ih hj, ← Category.assoc, action_comp]
        rfl

private noncomputable def selfStep (Y : Paper.TypeCategory (τ := τ) Φ) (m : Mode) : ofType P ⟶ Y ⨿ ofType P :=
  action P m ≫ coprod.inr

private theorem iterate_selfStep (Y : Paper.TypeCategory (τ := τ) Φ) (m : Mode) :
    iterate (selfStep P Y m) = iterate (coprod.inr : ofType P ⟶ Y ⨿ ofType P) := by
  cases m with
  | none => rw [selfStep, action, Category.id_comp]
  | some closed => exact ResetTables.iterate_selfStep closed.property Y .literal

theorem action_before_self (Y : Paper.TypeCategory (τ := τ) Φ) (m : Mode) :
    action P m ≫ iterate (coprod.inr : ofType P ⟶ Y ⨿ ofType P) = iterate coprod.inr := by
  cases m with
  | none => exact Category.id_comp _
  | some closed => exact ResetTables.action_before_self closed.property Y .literal

private theorem iterate_of_cut (B A : Shape) (p : A.Row → OutputCode (ClosedValue Φ P) B A) (mark : A.Row → Bool)
    (out : A.Row → OutputCode (ClosedValue Φ P) B A) (fuel : Nat)
    (computed : ∀ i, run (cutRows p mark) fuel i = some ⟨(out i).tag, (out i).reset⟩) :
    iterate (step P B A p) = iterate (step P B A out) := by
  let cut := stepWith P A (B := .sum B A) (ForwardingTables.output P B A) (cutRows p mark)
  have inner : iterate cut = step P B A out := hom_ext P A fun i => by
    rw [inj_step]
    exact iterate_runWith P (.sum B A) A (ForwardingTables.output P B A) (cutRows p mark) (computed i)
  have collapse : cut ≫ coprod.desc (𝟙 (obj P B ⨿ obj P A)) coprod.inr = step P B A p := by
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

private theorem iterate_row_recur (B A : Shape) (p : A.Row → OutputCode (ClosedValue Φ P) B A) {i j : A.Row}
    {m : Mode} (e : p i = ⟨.inr j, m⟩) :
    inj P A i ≫ iterate (step P B A p) = action P m ≫ (inj P A j ≫ iterate (step P B A p)) := by
  rw [iterate_row, e]
  simp only [outputWith, ForwardingTables.outputWith, Category.assoc, coprod.inr_desc]

private theorem iterate_row_self (B A : Shape) (p : A.Row → OutputCode (ClosedValue Φ P) B A) (i : A.Row)
    {m : Mode} (e : p i = ⟨.inr i, m⟩) :
    inj P A i ≫ iterate (step P B A p) =
      iterate (coprod.inr : ofType P ⟶ obj P B ⨿ ofType P) := by
  obtain ⟨a, ha, row⟩ := inj_is_branch (Φ := Φ) P A i
  have square : selfStep P (obj P B) m ≫ coprod.map (𝟙 (obj P B)) (inj P A i) =
      inj P A i ≫ step P B A p := by
    rw [inj_step, e, selfStep]
    simp only [outputWith, ForwardingTables.outputWith, Category.assoc, coprod.inr_map]
  rw [row] at square ⊢
  exact (iterate_uniformity_ofBranchValue ha _ _ square).symm.trans (iterate_selfStep P _ m)

theorem iterate_nonexit_row (B A : Shape) (p : A.Row → OutputCode (ClosedValue Φ P) B A) (i : A.Row)
    (infinite : ¬ ReachesExit p i) :
    inj P A i ≫ iterate (step P B A p) =
      iterate (coprod.inr : ofType P ⟶ obj P B ⨿ ofType P) := by
  obtain ⟨mark, fuel, out, computed, exits, returns⟩ := exists_summary B A p
  rw [iterate_of_cut P B A p mark out fuel computed]
  cases dest : (out i).tag with
  | inl b => exact False.elim (infinite (exits i b dest))
  | inr j =>
    have edge : out i = ⟨.inr j, (out i).reset⟩ :=
      congrArg (fun t => (⟨t, (out i).reset⟩ : OutputCode (ClosedValue Φ P) B A)) dest
    have self : out j = ⟨.inr j, (out j).reset⟩ :=
      congrArg (fun t => (⟨t, (out j).reset⟩ : OutputCode (ClosedValue Φ P) B A)) (returns i j dest)
    rw [iterate_row_recur P B A out edge, iterate_row_self P B A out j self, action_before_self]

theorem iterate_of_codes (B A D : Shape) (rows : A.Row → StateCode (ClosedValue Φ P) D)
    (p : A.Row → OutputCode (ClosedValue Φ P) B A) (q : D.Row → OutputCode (ClosedValue Φ P) B D)
    (square : ∀ i, (p i).mapState rows = (q (rows i).tag).withInput (rows i).reset) :
    iterate (step P B A p) = stateMap P A D rows ≫ iterate (step P B D q) := by
  classical
  apply hom_ext P A
  intro i
  rw [← Category.assoc, inj_stateMap, Category.assoc]
  by_cases exits : ReachesExit p i
  · obtain ⟨n, o, hp⟩ := exits
    have both := (run_simulates B A D rows p q square n i).symm.trans hp
    obtain ⟨target, ht, rfl⟩ := Option.map_eq_some_iff.mp both
    rw [iterate_runWith P B A (inj P B) p hp, iterate_runWith P B D (inj P B) q ht,
      ← Category.assoc, action_comp]
    rfl
  · have later : ¬ ReachesExit q (rows i).tag := by
      rintro ⟨n, o, h⟩
      have e := run_simulates B A D rows p q square n i
      rw [h, Option.map_some] at e
      exact exits ⟨n, _, e⟩
    rw [iterate_nonexit_row P B A p i exits, iterate_nonexit_row P B D q (rows i).tag later,
      action_before_self]

private theorem output_precomp (B A : Shape) (m : Mode) (o : OutputCode (ClosedValue Φ P) B A) :
    action P m ≫ output P B A o = output P B A (o.withInput m) := by
  change action P m ≫ (action P o.reset ≫ _) = _
  rw [← Category.assoc, action_comp]
  rfl

private theorem square_left (B A D : Shape) (rows : A.Row → StateCode (ClosedValue Φ P) D)
    (p : A.Row → OutputCode (ClosedValue Φ P) B A) (i : A.Row) :
    inj P A i ≫ (step P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D rows)) =
      output P B D ((p i).mapState rows) := by
  rw [← Category.assoc, inj_step]
  rcases row : p i with ⟨tag, m⟩
  cases tag with
  | inl b => simp [Code.mapState, outputWith, ForwardingTables.outputWith, Category.assoc]
  | inr j =>
    simp only [Code.mapState, outputWith, ForwardingTables.outputWith, Category.assoc, coprod.inr_map]
    rw [← Category.assoc (inj P A j), inj_stateMap]
    simp only [Category.assoc]
    rw [← Category.assoc (action P m), action_comp]

private theorem square_right (B A D : Shape) (rows : A.Row → StateCode (ClosedValue Φ P) D)
    (q : D.Row → OutputCode (ClosedValue Φ P) B D) (i : A.Row) :
    inj P A i ≫ (stateMap P A D rows ≫ step P B D q) =
      output P B D ((q (rows i).tag).withInput (rows i).reset) := by
  rw [← Category.assoc, inj_stateMap, Category.assoc, inj_step, output_precomp]

theorem square_of_codes (B A D : Shape) (rows : A.Row → StateCode (ClosedValue Φ P) D)
    (p : A.Row → OutputCode (ClosedValue Φ P) B A) (q : D.Row → OutputCode (ClosedValue Φ P) B D)
    (square : ∀ i, (p i).mapState rows = (q (rows i).tag).withInput (rows i).reset) :
    step P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D rows) =
      stateMap P A D rows ≫ step P B D q := by
  apply hom_ext P A
  intro i
  rw [square_left, square_right, square]

theorem projected_row_eq (B A D : Shape) (rows : A.Row → StateCode (ClosedValue Φ P) D)
    (p : A.Row → OutputCode (ClosedValue Φ P) B A) (q : D.Row → OutputCode (ClosedValue Φ P) B D)
    (comm : projection.map (step P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D rows)) =
      projection.map (stateMap P A D rows ≫ step P B D q)) (i : A.Row) :
    projection.map (output P B D ((p i).mapState rows)) =
      projection.map (output P B D ((q (rows i).tag).withInput (rows i).reset)) := by
  have e := congrArg (projection.map (inj P A i) ≫ ·) comm
  rw [← projection.map_comp, ← projection.map_comp, square_left, square_right] at e
  exact e

theorem projected_action_eq (B A : Shape) (x y : OutputCode (ClosedValue Φ P) B A)
    (agree : projection.map (output P B A x) = projection.map (output P B A y)) :
    projection.map (action P x.reset) = projection.map (action P y.reset) := by
  let untag : obj (Φ := Φ) P B ⨿ obj P A ⟶ ofType P :=
    coprod.desc (table P B fun _ => 𝟙 (ofType P)) (table P A fun _ => 𝟙 (ofType P))
  have cancels (o : OutputCode (ClosedValue Φ P) B A) :
      output P B A o ≫ untag = action P o.reset := by
    rcases o with ⟨tag, m⟩
    cases tag <;> simp only [outputWith, ForwardingTables.outputWith, untag, Category.assoc,
      coprod.inl_desc, coprod.inr_desc, inj_table, Category.comp_id]
  have e := congrArg (· ≫ projection.map untag) agree
  rw [← projection.map_comp, ← projection.map_comp, cancels, cancels] at e
  exact e

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultiple
