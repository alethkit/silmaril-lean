module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.MultiNested.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgFiniteSyntax
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMultiSyntax
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.SlotMaps.Boundary.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.SlotMaps.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Pruning.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.ReplaceNewest.Thms

/-! # Exact comparison of a checked table with several selected nested rows -/

public section

universe v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMultiAdmission

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.MultiNested
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

private def payloadType (A D : Ty Empty) : Bool → Ty Empty
  | false => A
  | true => .coprod A D

private abbrev wideTypes {m : Nat} (P : Fin m → Ty Empty) (forms : Fin m → Bool) (D : Fin m → Ty Empty) :=
  fun i => payloadType (P i) (D i) (forms i)

private abbrev labels {m : Nat} (P : Fin m → Ty Empty) (L : LCtx (Ty Empty)) := List.ofFn P ++ L
private abbrev single (A : Ty Empty) : Fin 1 → Ty Empty := fun _ => A

private theorem localAt {m : Nat} (P : Fin m → Ty Empty) (L : LCtx (Ty Empty)) (i : Fin m) :
    At (labels P L) i (P i) := by simp [At, labels, List.getElem?_append_left, i.isLt]

private theorem exitAt {m : Nat} (P : Fin m → Ty Empty) {L : LCtx (Ty Empty)} {i : Nat} {A : Ty Empty}
    (h : At L i A) : At (labels P L) (m+i) A := by
  simpa [At, labels, List.getElem?_append_right] using h

section Maps

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel (Ty Empty) V)

private noncomputable abbrev inLeft (A D : Ty Empty) : M.obj A ⟶ M.obj (.coprod A D) :=
  coprod.inl ≫ (M.coprodIso A D).inv

private noncomputable def payloadMap (A D : Ty Empty) (t : Bool) :
    M.obj A ⟶ M.obj (payloadType A D t) :=
  match t with
  | false => 𝟙 _
  | true => inLeft M A D

private noncomputable abbrev slot {m : Nat} (P : Fin m → Ty Empty) (F : Fin m → Bool) (D : Fin m → Ty Empty) :
    ∀ i, M.obj (P i) ⟶ M.obj (wideTypes P F D i) :=
  fun i => payloadMap M (P i) (D i) (F i)

/-- The checked transfer law is phrased on label injections, independently
of any row or iteration witness. -/
private structure Coordinates (out : RouteLayout Empty) {K W : LCtx (Ty Empty)}
    (post : labelObj M K ⟶ labelObj M W) : Prop where
  plain : ∀ i A, out[i]? = some (A, false) →
    ∃ (hl : At K i A) (hr : At W i A), labelInject M i hl ≫ post = labelInject M i hr
  left : ∀ i A, out[i]? = some (A, true) →
    ∃ (D : Ty Empty) (hl : At K i A) (hr : At W i (.coprod A D)),
      labelInject M i hl ≫ post = inLeft M A D ≫ labelInject M i hr

private theorem local_plain {K : LCtx (Ty Empty)} {i : Nat} {A D : Ty Empty} {t : Bool}
    (eq : t = false) (h : At K i (payloadType A D t)) (h' : At K i A) :
    payloadMap M A D t ≫ labelInject M i h = labelInject M i h' := by
  subst t
  exact Category.id_comp _

private theorem local_left {K : LCtx (Ty Empty)} {i : Nat} {A D : Ty Empty} {t : Bool}
    (eq : t = true) (h : At K i (payloadType A D t)) (h' : At K i (.coprod A D)) :
    payloadMap M A D t ≫ labelInject M i h = inLeft M A D ≫ labelInject M i h' := by
  subst t
  rfl

private theorem coordinates {m : Nat} (P : Fin m → Ty Empty) (F : Fin m → Bool) (D : Fin m → Ty Empty)
    (L : LCtx (Ty Empty)) : Coordinates M (layout P F L) (mapSlotBoundary M (slot M P F D) L) := by
  let W := wideTypes P F D
  have lookup {i : Nat} (hi : i < m) :
      (layout P F L)[i]? = some (P ⟨i, hi⟩, F ⟨i, hi⟩) := by
    simp [layout, List.getElem?_append_left, hi]
  have outward (i : Nat) : (layout P F L)[m + i]? = (L.map (fun A => (A, false)))[i]? := by
    simp [layout, List.getElem?_append_right]
  constructor
  · intro i A hit
    by_cases hi : i < m
    · let j : Fin m := ⟨i, hi⟩
      obtain ⟨same, flag⟩ := Prod.mk.inj (Option.some.inj ((lookup hi).symm.trans hit))
      change P j = A at same
      subst A
      have h : At (labels W L) j (W j) := localAt W L j
      change F j = false at flag
      have ht : At (labels W L) j (P j) := by
        change At (labels W L) j (payloadType (P j) (D j) (F j)) at h
        simpa only [flag, payloadType] using h
      exact ⟨localAt P L j, ht, (mapSlotBoundary_local M (slot M P F D) L j _ h).trans
        (local_plain M flag h ht)⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = m + j := ⟨i-m, by omega⟩
      rw [outward, List.getElem?_map] at hit
      obtain ⟨B, get, eq⟩ := Option.map_eq_some_iff.mp hit
      have h : At L j A := get.trans (congrArg (fun x : Ty Empty × Bool => some x.1) eq)
      exact ⟨exitAt P h, exitAt W h, mapSlotBoundary_exit M (slot M P F D) L h _ _⟩
  · intro i A hit
    by_cases hi : i < m
    · let j : Fin m := ⟨i, hi⟩
      obtain ⟨same, flag⟩ := Prod.mk.inj (Option.some.inj ((lookup hi).symm.trans hit))
      change P j = A at same
      subst A
      have h : At (labels W L) j (W j) := localAt W L j
      change F j = true at flag
      have ht : At (labels W L) j (.coprod (P j) (D j)) := by
        change At (labels W L) j (payloadType (P j) (D j) (F j)) at h
        simpa only [flag, payloadType] using h
      exact ⟨D j, localAt P L j, ht, (mapSlotBoundary_local M (slot M P F D) L j _ h).trans
        (local_left M flag h ht)⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = m + j := ⟨i-m, by omega⟩
      rw [outward, List.getElem?_map] at hit
      obtain ⟨_, _, eq⟩ := Option.map_eq_some_iff.mp hit
      cases eq

private theorem leaf_routes {out : RouteLayout Empty} {K W : LCtx (Ty Empty)}
    {post : labelObj M K ⟶ labelObj M W} (coord : Coordinates M out post)
    {Γ : VCtx (Ty Empty)} {r s : Region Φ} (checked : CheckedRoutes out Γ r s) :
    RegionConstructorRoutes M post (𝟙 _) Γ r s := by
  apply CheckedRoutes.toConstructorRoutes M checked
  · intro i A h
    obtain ⟨l, r, e⟩ := coord.plain i A h
    exact ⟨l, r, e.trans (Category.comp_id _).symm⟩
  · intro i A h
    obtain ⟨D, l, r, e⟩ := coord.left i A h
    exact ⟨D, l, r, by rw [Category.comp_id]; exact e⟩

private theorem inner_routes {out : RouteLayout Empty} {K W : LCtx (Ty Empty)}
    {post : labelObj M K ⟶ labelObj M W} (coord : Coordinates M out post) (A : Ty Empty)
    {Γ : VCtx (Ty Empty)} {r s : Region Φ} (checked : CheckedRoutes ((A, false) :: out) Γ r s) :
    RegionConstructorRoutes M
      (labelAppendSplit M (List.ofFn (single A)) K ≫ coprod.map post (𝟙 _)) (labelAppendSplit M (List.ofFn (single A)) W) Γ r s := by
  have liftExit {i : Nat} {B T : Ty Empty} (l : At K i B) (r : At W i T) (f : M.obj B ⟶ M.obj T)
      (h : labelInject M i l ≫ post = f ≫ labelInject M i r) :
      labelInject M (1+i) (exitAt (single A) l) ≫ (labelAppendSplit M (List.ofFn (single A)) K ≫ coprod.map post (𝟙 _)) =
        f ≫ labelInject M (1+i) (exitAt (single A) r) ≫ labelAppendSplit M (List.ofFn (single A)) W := by
    rw [← Category.assoc, labelAppendSplit_exit M (single A) K l, Category.assoc,
      coprod.inl_map, ← Category.assoc, h, Category.assoc, labelAppendSplit_exit M (single A) W r]
  apply CheckedRoutes.toConstructorRoutes M checked
  · intro i B hit
    cases i with
    | zero =>
        have eq : A = B := congrArg Prod.fst (Option.some.inj hit)
        subst B
        refine ⟨localAt (single A) K 0, localAt (single A) W 0, ?_⟩
        erw [← Category.assoc, labelAppendSplit_local M (single A) K 0 _ rfl, Category.assoc,
          coprod.inr_map, Category.id_comp, labelAppendSplit_local M (single A) W 0 _ rfl]
    | succ i =>
        obtain ⟨l, r, h⟩ := coord.plain i B hit
        have e := liftExit l r (𝟙 _) (h.trans (Category.id_comp _).symm)
        rw [Category.id_comp] at e
        have hl : At (labels (single A) K) (i + 1) B := l
        have hr : At (labels (single A) W) (i + 1) B := r
        exact ⟨hl, hr, by simpa only [Nat.add_comm 1 i] using e⟩
  · intro i B hit
    cases i with
    | zero => simp at hit
    | succ i =>
        obtain ⟨D, l, r, h⟩ := coord.left i B hit
        have hl : At (labels (single A) K) (i + 1) B := l
        have hr : At (labels (single A) W) (i + 1) (.coprod B D) := r
        exact ⟨D, hl, hr, by simpa only [Nat.add_comm 1 i] using liftExit l r (inLeft M B D) h⟩

end Maps


section Model

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Φ]

local notation "Env" => ctxObj M []

private theorem read_inner {A : Ty Empty} {K : LCtx (Ty Empty)} {r : Region Φ}
    {t : (inner r).HasType [A] K} {f : J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M K)}
    (d : RegionDenotes J M t f) :
    CfgDenotesAt J M (single A) (.br 0 (.var 0)) (fun _ => r) f := by
  apply d.cfg_readback_of_labels_determined J M
  intro S he _
  have eq : S 0 = A := by
    cases he with
    | br hit ht =>
        cases ht with
        | var var =>
            exact Option.some.inj ((localAt S K 0).symm.trans hit |>.trans var.symm)
  exact funext (Fin.cases eq fun i => Fin.elim0 i)

private theorem select_inner {A D : Ty Empty} {K : LCtx (Ty Empty)} {raw row : Region Φ}
    (prune : Region.PruneConstructorTests (raw.substVars (Tm.replaceNewest (.inl (.var 0)))) (inner row))
    {t : raw.HasType [.coprod A D] K} {b : J.obj (ctxObj M [.coprod A D]) ⟶ J.obj (labelObj M K)}
    (w : RegionDenotes J M t b) :
    ∃ h : (inner row).HasType [A] K, RegionDenotes J M h (J.map (Env ◁ inLeft M A D) ≫ b) := by
  have da : Denotes J M (.inl (.var rfl) (B := D) : (Tm.inl (.var 0) : Tm Φ).HasType [A] (.coprod A D))
      (J.map (snd Env (M.obj A) ≫ inLeft M A D)) := by
    rw [J.map_comp]
    exact .inl (.var rfl)
  obtain ⟨_, restricted⟩ := w.replaceNewest J M da
  exact prune.denotes J M restricted

private theorem inner_compare {A : Ty Empty} {K W : LCtx (Ty Empty)} {out : RouteLayout Empty}
    {post : labelObj M K ⟶ labelObj M W} (coord : Coordinates M out post)
    {r s : Region Φ} (check : CheckedRoutes ((A, false) :: out) [A, A] r s)
    {tl : (inner r).HasType [A] K} {tr : (inner s).HasType [A] W}
    {f : J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M K)}
    {g : J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M W)}
    (left : RegionDenotes J M tl f) (right : RegionDenotes J M tr g) : g = f ≫ J.map post := by
  have entry : CheckedRoutes (Φ := Φ) ((A, false) :: out) [A] (.br 0 (.var 0)) (.br 0 (.var 0)) :=
    .plain rfl (.var rfl) (.var rfl)
  exact CfgDenotesAt.postmap_of_routes J M (single A) post
    (RegionConstructorRoutes.denotes J M (inner_routes M coord A entry))
    (fun _ => RegionConstructorRoutes.denotes J M (inner_routes M coord A check))
    (read_inner J M left) (read_inner J M right)

private theorem row_anchor {m : Nat} {P S : Fin m → Ty Empty} {F : Fin m → Bool}
    {L : LCtx (Ty Empty)} {A B : Ty Empty} {form : Bool} {raw : Region Φ} {p : RowPlan Φ}
    (row : p.Valid A (layout P F L) raw form) (fit : NestedCfgMultiSyntax.Fits A form B)
    {h : raw.HasType [B] (labels S L)} {f : J.obj (ctxObj M [B]) ⟶ J.obj (labelObj M (labels S L))}
    (d : RegionDenotes J M h f) (i : Fin m) (edge : p.targets i = true) :
    NestedCfgMultiSyntax.Fits (P i) (F i) (S i) := by
  cases row with
  | ordinary route =>
      change B = A at fit
      subst B
      exact NestedCfgMultiSyntax.target [] route h i (by simpa [RowPlan.targets] using edge)
  | nested prune route =>
      obtain ⟨D, rfl⟩ := fit
      obtain ⟨_, selected⟩ := select_inner J M prune d
      obtain ⟨_, rows, _⟩ := read_inner J M selected
      exact NestedCfgMultiSyntax.target [(A, false)] route (rows 0) i edge

private theorem row_eq {A D : Ty Empty} {form : Bool} {out : RouteLayout Empty}
    {K W : LCtx (Ty Empty)} {post : labelObj M K ⟶ labelObj M W} (coord : Coordinates M out post)
    {raw : Region Φ} {p : RowPlan Φ} (checked : p.Valid A out raw form)
    {tl : p.commonRegion.HasType [A] K} {tw : raw.HasType [payloadType A D form] W}
    {f : J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M K)}
    {g : J.obj (ctxObj M [payloadType A D form]) ⟶ J.obj (labelObj M W)}
    (left : RegionDenotes J M tl f) (right : RegionDenotes J M tw g) :
    J.map (Env ◁ payloadMap M A D form) ≫ g = f ≫ J.map post := by
  cases checked with
  | ordinary route =>
      have eq := RegionConstructorRoutes.denotes J M (leaf_routes M coord (Region.checkRoutes?_sound route)) left right
      rw [J.map_id, Category.comp_id] at eq
      change J.map (Env ◁ 𝟙 (M.obj A)) ≫ g = _
      rw [MonoidalCategory.whiskerLeft_id, J.map_id, Category.id_comp]
      exact eq.symm
  | nested prune route =>
      obtain ⟨_, selected⟩ := select_inner J M prune right
      exact inner_compare J M coord (Region.checkRoutes?_sound route) left selected

variable {m n : Nat} {keep : Fin (m + 1) ↪ Fin (n + 1)} {P : Fin (m + 1) → Ty Empty}
  {F : Fin (m + 1) → Bool} {r : Region Φ} {L : LCtx (Ty Empty)} {p : Plan Φ (m + 1) (n + 1)}

local notation "Arrow" => J.obj Env ⟶ J.obj (labelObj M L)
local notation "ActualRows" => fun i => p.outer.rows (keep i)
local notation "CommonRows" => fun i => RowPlan.commonRegion (p.rows i)

private theorem align (ok : p.Valid keep P F r L) {S : Fin (m + 1) → Ty Empty}
    {f : Arrow} (d : CfgDenotesAt J M S p.outer.entry ActualRows f) :
    ∃ D : Fin (m + 1) → Ty Empty, S = wideTypes P F D := by
  obtain ⟨he, _, _, _, _, _, rows, _⟩ := d
  have initial (i : Fin (m + 1)) (hit : NestedAdmission.Finite.branchesTo i p.entry = true) :
      NestedCfgMultiSyntax.Fits (P i) (F i) (S i) :=
    NestedCfgMultiSyntax.target [] ok.entry he i (by simpa using hit)
  have advance (j i : Fin (m + 1)) (fit : NestedCfgMultiSyntax.Fits (P j) (F j) (S j))
      (edge : (p.rows j).targets i = true) :
      NestedCfgMultiSyntax.Fits (P i) (F i) (S i) :=
    row_anchor J M (ok.rows j) fit (rows j) i edge
  have tails (i : Fin (m + 1)) : ∃ D, S i = payloadType (P i) D (F i) := by
    have fit := NestedCfgFiniteSyntax.of_worklist initial advance (ok.anchors i)
    cases hi : F i with
    | false => exact ⟨.empty, by simpa [NestedCfgMultiSyntax.Fits, payloadType, hi] using fit⟩
    | true => simpa [NestedCfgMultiSyntax.Fits, payloadType, hi] using fit
  choose D eq using tails
  exact ⟨D, funext eq⟩

private theorem compare_reduced (ok : p.Valid keep P F r L) (D : Fin (m + 1) → Ty Empty)
    {f g : Arrow} (small : CfgDenotesAt J M P p.entry CommonRows f)
    (wide : CfgDenotesAt J M (wideTypes P F D) p.outer.entry ActualRows g) : f = g := by
  let post := mapSlotBoundary M (slot M P F D) L
  have coord := coordinates M P F D L
  have split_eq {Γ : VCtx (Ty Empty)}
      {a : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (labels P L))}
      {b : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (labels (wideTypes P F D) L))}
      (h : b = a ≫ J.map post) :
      b ≫ J.map (labelAppendSplit M (List.ofFn (wideTypes P F D)) L) =
        a ≫ J.map (labelAppendSplit M (List.ofFn P) L) ≫
          J.map (coprod.map (𝟙 _) (mapSlotLabels M (slot M P F D))) := by
    rw [h, Category.assoc, ← J.map_comp, mapSlotBoundary_split, J.map_comp]
  have mapped := CfgDenotesAt.postmap_of_slot_squares J M (slot M P F D) (𝟙 (labelObj M L))
    (fun _ _ _ _ dl dr => by
      have eq := RegionConstructorRoutes.denotes J M (leaf_routes M coord (Region.checkRoutes?_sound ok.entry)) dl dr
      rw [J.map_id, Category.comp_id] at eq
      exact split_eq eq.symm)
    (fun i _ _ a b dl dr => by
      have eq := row_eq J M (D := D i) coord (ok.rows i) dl dr
      have component := split_eq (Γ := [P i]) (a := a) (b := J.map (Env ◁ slot M P F D i) ≫ b) eq
      rw [Category.assoc] at component
      exact component)
    small wide
  rwa [J.map_id, Category.comp_id, eq_comm] at mapped

private theorem common_type {out : RouteLayout Empty} {A : Ty Empty} {form : Bool} {raw : Region Φ}
    {row : RowPlan Φ} (ok : row.Valid A out raw form) : row.commonRegion.HasType [A] (out.map Prod.fst) := by
  cases ok with
  | ordinary h => exact (Region.checkRoutes?_sound h).hasType
  | nested prune route =>
      exact .cfg (single A) (.br rfl (.var rfl)) (fun _ => (Region.checkRoutes?_sound route).hasType)

private theorem compare_checked (roll : IterationRolling C) (ok : p.Valid keep P F r L)
    {h h' : r.HasType [] L} {f g : Arrow}
    (left : RegionDenotes J M h f) (right : RegionDenotes J M h' g) : f = g := by
  have shape : (layout P F L).map Prod.fst = labels P L := by
    simp [layout, labels, List.map_ofFn, Function.comp_def, List.map_map]
  obtain ⟨base, small⟩ := CfgDenotesAt.exists_of_typing J M P (L := L)
    (shape ▸ (Region.checkRoutes?_sound ok.entry).hasType) (fun i => shape ▸ common_type (ok.rows i))
  have agree {ht : r.HasType [] L} {b : Arrow} (w : RegionDenotes J M ht b) : base = b := by
    obtain ⟨_, _, trimmed⟩ := ok.outer.readback J M roll w
    obtain ⟨D, eq⟩ := align J M ok trimmed
    rw [eq] at trimmed
    exact compare_reduced J M ok D small trimmed
  exact (agree left).symm.trans (agree right)

theorem compare (roll : IterationRolling C) (ok : compare? keep P F r L = .certified)
    {h h' : r.HasType [] L} {f g : Arrow}
    (left : RegionDenotes J M h f) (right : RegionDenotes J M h' g) : f = g := by
  cases found : check? keep P F r L with
  | none => simp [compare?, found] at ok
  | some p => exact compare_checked J M roll (NestedCfgMultiSyntax.checked found) left right

end Model

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMultiAdmission
