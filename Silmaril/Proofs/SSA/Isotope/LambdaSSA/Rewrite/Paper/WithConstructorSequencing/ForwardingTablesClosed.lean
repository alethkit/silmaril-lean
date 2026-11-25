module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ForwardingTables.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.Observation.Thms

/-! # Detecting forwarded tags on instruction-free payloads -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTablesClosed

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Paper.WithConstructorSequencing ForwardingTables
open UnitSumSquare (Shape)
open UnitSumSquare.Cycles.Mixed.MergeCycle (result source target tags sourceRows targetRows)
open scoped Paper.BoundSimulation.Obstruction
open Silmaril.DeBruijn (lift)

set_option backward.isDefEq.respectTransparency false

theorem separates_of_closed {P : Ty Empty} {w : Tm Empty} (hw : Tm.BranchValue [] w P) :
    SeparatesTags (Φ := Empty) P := by
  intro eq
  rw [← sumCofan_inl_sumIso_hom P P, ← sumCofan_inr_sumIso_hom P P,
    projection.map_comp, projection.map_comp] at eq
  have h := (cancel_mono (projection.map (sumIso P P).hom)).mp eq
  rw [sumCofan_inl, sumCofan_inr] at h
  have typed := (Paper.Extension.Singleton.ofRegion_eq_iff Seed
    (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl)))
    (.br (ℓ := 0) rfl (.inr (.var (i := 0) rfl)))).mp h
  have observed := Paper.BoundSimulation.Obstruction.PairSequencing.branch_observation_of_closed_input
    (.inl (.var (i := 0) rfl)) (.inr (.var (i := 0) rfl)) hw typed
  cases observed

private theorem case_ignoring {A B : Ty Empty} {Γ L : List (Ty Empty)} {r : Region Empty}
    {i : Nat} (hi : At Γ i (.coprod A B)) (hr : Region.HasType Γ r L) :
    Paper.Eqv Γ (.case (.var i) (r.renameVars Nat.succ) (r.renameVars Nat.succ)) r L := by
  have e := SubstitutionEquiv.caseValue (.var hi) (hr.renameVars (Ren.wk Γ (.coprod A B)))
  have skip (a : Tm Empty) : Tm.replaceNewest a ∘ Nat.succ = Tm.var ∘ Nat.succ := rfl
  have drop : Tm.singleSubst (Tm.var (Φ := Empty) i) ∘ Nat.succ = Tm.var := rfl
  apply Paper.Eqv.cfgEta
  apply CfgEta.Eqv.native
  simpa only [substVars_renameVars, skip, drop, substVars_var, ← renameVars_eq_substVars] using e

private theorem unpack_ignoring {A B : Ty Empty} {Γ L : List (Ty Empty)} {r : Region Empty}
    {i : Nat} (hi : At Γ i (.product A B)) (hr : Region.HasType Γ r L) :
    Paper.Eqv Γ (.let₂ (.var i) (r.renameVars (Nat.succ ∘ Nat.succ))) r L := by
  let eta : Paper.Eqv (Φ := Empty) Γ (.let₂ (.var i) (.br 0 (.pair (.var 1) (.var 0))))
      (.br 0 (.var i)) [.product A B] := .productEta (.let₂Eta hi rfl)
  have hσ : LSubst.HasType Γ [.product A B] L (fun _ => r.renameVars Nat.succ) := by
    intro _ C hC
    have h : C = .product A B := List.mem_singleton.mp (List.mem_of_getElem? hC)
    subst C
    exact hr.renameVars (Ren.wk Γ _)
  have e := eta.lsubstPost
    (.let₂ (.var hi) (.br rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))
    (.br rfl (.var hi)) hσ
  have drop : Tm.singleSubst (Tm.var (Φ := Empty) i) ∘ Nat.succ = Tm.var := rfl
  have inserted : Tm.singleSubst (Tm.pair (Φ := Empty) (.var 1) (.var 0)) ∘
      (lift Nat.succ ∘ (lift Nat.succ ∘ Nat.succ)) = Tm.var ∘ (Nat.succ ∘ Nat.succ) := rfl
  simpa only [lsubst, liftLSubstVars, renameVars_comp, substVars_renameVars, drop, inserted,
    substVars_var, ← renameVars_eq_substVars] using e

private inductive EmptyPayload : Ty Empty → Prop
  | empty : EmptyPayload .empty
  | sum {A B : Ty Empty} : EmptyPayload A → EmptyPayload B → EmptyPayload (.coprod A B)
  | left {A B : Ty Empty} : EmptyPayload A → EmptyPayload (.product A B)
  | right {A B : Ty Empty} : EmptyPayload B → EmptyPayload (.product A B)

private theorem closed_or_empty (P : Ty Empty) :
    (∃ w : Tm Empty, Tm.BranchValue [] w P) ∨ EmptyPayload P := by
  induction P with
  | base a => exact a.elim
  | empty => exact .inr .empty
  | unit => exact .inl ⟨.unit, .unit⟩
  | coprod A B ihA ihB =>
    rcases ihA with ⟨a, ha⟩ | hA
    · exact .inl ⟨.inl a, .inl ha⟩
    · rcases ihB with ⟨b, hb⟩ | hB
      · exact .inl ⟨.inr b, .inr hb⟩
      · exact .inr (.sum hA hB)
  | product A B ihA ihB =>
    rcases ihA with ⟨a, ha⟩ | hA
    · rcases ihB with ⟨b, hb⟩ | hB
      · exact .inl ⟨.pair a b, .pair ha hb⟩
      · exact .inr (.right hB)
    · exact .inr (.left hA)

private theorem empty_context {P : Ty Empty} (hP : EmptyPayload P)
    {Γ L : List (Ty Empty)} {i : Nat} (hi : At Γ i P) {r s : Region Empty}
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L) : Paper.Eqv Γ r s L := by
  induction hP generalizing Γ i r s with
  | empty => exact .cfgEta (.native (.initial (.var hi) hr hs))
  | @sum A B _ _ ihA ihB =>
    have left : Ren Γ (A :: Γ) Nat.succ := Ren.wk Γ A
    have right : Ren Γ (B :: Γ) Nat.succ := Ren.wk Γ B
    exact (case_ignoring hi hr).symm.trans
      ((Paper.Eqv.case (.var hi)
        (ihA (i := 0) rfl (hr.renameVars left) (hs.renameVars left))
        (ihB (i := 0) rfl (hr.renameVars right) (hs.renameVars right))).trans (case_ignoring hi hs))
  | @left A B _ ih =>
    have shift := (Ren.wk Γ A).comp (Ren.wk (A :: Γ) B)
    exact (unpack_ignoring hi hr).symm.trans
      ((Paper.Eqv.let₂ (.var hi)
        (ih (i := 1) rfl (hr.renameVars shift) (hs.renameVars shift))).trans (unpack_ignoring hi hs))
  | @right A B _ ih =>
    have shift := (Ren.wk Γ A).comp (Ren.wk (A :: Γ) B)
    exact (unpack_ignoring hi hr).symm.trans
      ((Paper.Eqv.let₂ (.var hi)
        (ih (i := 0) rfl (hr.renameVars shift) (hs.renameVars shift))).trans (unpack_ignoring hi hs))

private theorem empty_payload_initial {P : Ty Empty} (hP : EmptyPayload P) :
    Nonempty (IsInitial (ofType (Φ := Empty) P)) := by
  have collapse {Y : Paper.TypeCategory Empty} (f g : ofType P ⟶ Y) : f = g := by
    obtain ⟨_, hf, rfl⟩ := exists_ofRegion f
    obtain ⟨_, hg, rfl⟩ := exists_ofRegion g
    exact (ofRegion_eq_iff hf hg).mpr (empty_context hP (i := 0) rfl hf.hasType hg.hasType)
  exact ⟨IsInitial.ofUniqueHom (fun Y => iterate (coprod.inr : ofType P ⟶ Y ⨿ ofType P))
    (fun _ f => collapse f _)⟩

theorem initial_of_no_closed_value (P : Ty Empty) (h : ¬ ∃ w : Tm Empty, Tm.BranchValue [] w P) :
    Nonempty (IsInitial (ofType (Φ := Empty) P)) := by
  exact empty_payload_initial ((closed_or_empty P).resolve_left h)

theorem separates_or_initial (P : Ty Empty) :
    SeparatesTags (Φ := Empty) P ∨ Nonempty (IsInitial (ofType (Φ := Empty) P)) := by
  rcases closed_or_empty P with ⟨w, hw⟩ | hP
  · exact .inl (separates_of_closed hw)
  · exact .inr (empty_payload_initial hP)

abbrev payload : Ty Empty := .product .unit (.coprod .unit .unit)

private theorem sample_separates : SeparatesTags (Φ := Empty) payload :=
  separates_of_closed (.pair .unit (.inl .unit))

theorem projected_square :
    projection.map (step (Φ := Empty) payload result source sourceRows ≫
      coprod.map (𝟙 (obj payload result)) (stateMap payload source target tags)) =
    projection.map (stateMap payload source target tags ≫ step payload result target targetRows) := by
  apply congrArg projection.map
  apply square_of_tags
  rintro ((i | i) | (i | i)) <;> cases i <;> rfl

theorem not_mono : ¬ Mono (stateMap (Φ := Empty) payload source target tags) := by
  intro mono
  let left : source.Row := .inl (.inl ())
  let right : source.Row := .inl (.inr ())
  have e : inj (Φ := Empty) payload source left = inj payload source right := by
    apply (cancel_mono (stateMap payload source target tags)).mp
    rw [stateMap, inj_table, inj_table]
    rfl
  have outputs : projection.map (output (Φ := Empty) payload source .empty (.inl left)) =
      projection.map (output (Φ := Empty) payload source .empty (.inl right)) :=
    congrArg (fun f => projection.map (f ≫ coprod.inl)) e
  have same := separate_output payload sample_separates source .empty outputs
  have tagsEqual := Sum.inl.inj same
  change (Sum.inl (Sum.inl ()) : source.Row) = Sum.inl (Sum.inr ()) at tagsEqual
  cases Sum.inl.inj tagsEqual

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTablesClosed
