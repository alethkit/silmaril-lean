module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmissionSyntax
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Check.Thms

/-! # Finite traversal and exact input-type readback -/

public section

universe v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgFiniteSyntax

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

theorem valid {k n : Nat} {keep : Fin (k + 1) ↪ Fin (n + 1)} {P : Fin (k + 1) → Ty Empty}
    {r : Region Φ} {p : Plan Φ (k + 1) (n + 1)} (ok : check? keep P r = some p) : p.Valid keep P r := by
  simp only [check?] at ok
  split at ok <;> try contradiction
  rename_i blocks
  simp only [Option.bind_eq_some_iff] at ok
  obtain ⟨body, chosen, ok⟩ := ok
  ·
      split at ok <;> try contradiction
      rename_i entry size rows
      split at ok <;> try contradiction
      rename_i sizeEq
      subst size
      simp only [Option.bind_eq_some_iff] at ok
      obtain ⟨e, he, bs, hbs, ce, hce, cs, hcs, ok⟩ := ok
      split at ok <;> try contradiction
      rename_i all
      cases Option.some.inj ok
      obtain ⟨scope, restore⟩ := Region.restrictLabels?_sound he
      have kept := fun i => Region.restrictLabels?_sound (Region.checkFamily_some hbs i)
      refine ⟨?_, ?_, scope, fun i => (kept i).1, hce, Region.checkFamily_some hcs, ?_⟩
      · congr 1
        funext i
        cases Subsingleton.elim i (0 : Fin 1)
        rfl
      · rw [restore, funext (fun i => (kept i).2)]
        exact NestedCfgAdmissionSyntax.selected chosen
      · intro i
        simpa using (List.all_eq_true.mp all i (List.mem_finRange _))

private theorem branch_type {Γ K : List (Ty Empty)} {i : Nat} {a : Tm Φ} {A : Ty Empty}
    (unique : TypeDetermined Γ a A) (typed : (Region.br i a).HasType Γ K) : At K i A := by
  cases typed with
  | br hit arg => simpa only [unique _ arg] using hit

private theorem case_types {Γ K : List (Ty Empty)} {a : Tm Φ} {l r : Region Φ} {A B : Ty Empty}
    (unique : TypeDetermined Γ a (.coprod A B)) (typed : (Region.case a l r).HasType Γ K) :
    l.HasType (A :: Γ) K ∧ r.HasType (B :: Γ) K := by
  cases typed with
  | case test yes no =>
      obtain ⟨rfl, rfl⟩ := Ty.coprod.inj (unique _ test)
      exact ⟨yes, no⟩

/-- A checked plain transfer along a written path fixes its exact target type,
on the common or original side. The surrounding label context is arbitrary. -/
theorem plain_target {layout : RouteLayout Empty} {Γ K : List (Ty Empty)} {r s : Region Φ}
    {i : Nat} {A : Ty Empty} (wide : Bool) (ok : r.checkRoutes? layout Γ = some s)
    (target : branchesTo i s = true) (localType : layout[i]? = some (A, false))
    (typed : (if wide then r else s).HasType Γ K) : At K i A := by
  induction r generalizing Γ s with
  | br j a =>
      cases hit : layout[j]? with
      | none => simp [Region.checkRoutes?, hit] at ok
      | some route =>
          obtain ⟨B, tag⟩ := route
          simp only [Region.checkRoutes?, hit, Option.bind_eq_some_iff] at ok
          obtain ⟨b, payload, rest⟩ := ok
          cases found : b.synthRouteType? Γ with
          | none => simp [found] at rest
          | some T =>
              simp only [found] at rest
              split at rest <;> try contradiction
              rename_i eq
              subst T
              cases Option.some.inj rest
              have ji : j = i := beq_iff_eq.mp target
              subst j
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hit.symm.trans localType))
              cases Option.some.inj payload
              have unique := (Tm.synthRouteType?_sound found).2.1
              cases wide <;> exact branch_type unique typed
  | case a l r il ir =>
      cases found : a.synthRouteType? Γ with
      | none => simp [Region.checkRoutes?, found] at ok
      | some T =>
          cases T <;> simp [Region.checkRoutes?, found, Option.bind_eq_some_iff] at ok
          obtain ⟨ls, hl, rs, hr, rfl⟩ := ok
          have unique := (Tm.synthRouteType?_sound found).2.1
          rename_i A B
          have arms : (if wide then l else ls).HasType (A :: Γ) K ∧
              (if wide then r else rs).HasType (B :: Γ) K := by
            cases wide <;> exact case_types unique typed
          rcases Bool.or_eq_true_iff.mp target with yes | no
          · exact il hl yes arms.1
          · exact ir hr no arms.2
  | let₁ | let₂ | cfg => contradiction

private theorem local_at {α : Type} {m : Nat} (P : Fin m → α) (L : List α) (i : Fin m) :
    (List.ofFn P ++ L)[i.val]? = some (P i) := by
  simp [List.getElem?_append_left, i.isLt]

theorem aligned {m n : Nat} {keep : Fin m ↪ Fin n} {P S : Fin m → Ty Empty}
    {K : List (Ty Empty)} {entry commonEntry : Region Φ} {rows : Fin n → Region Φ}
    {commonRows : Fin m → Region Φ} (wide : Bool)
    (er : entry.checkRoutes? (layout P) [NestedAdmission.unitTy] = some commonEntry)
    (rr : ∀ i, (rows (keep i)).checkRoutes? (layout P) [P i, NestedAdmission.unitTy] = some (commonRows i))
    (typedEntry : (if wide then entry else commonEntry).HasType [NestedAdmission.unitTy] (List.ofFn S ++ K))
    (typedRows : ∀ i, (if wide then rows (keep i) else commonRows i).HasType
      [S i, NestedAdmission.unitTy] (List.ofFn S ++ K))
    {d : Nat} (paths : ∀ i, i ∈ anchored commonEntry commonRows d) : S = P := by
  have entryFixed (i : Fin m) (h : branchesTo i commonEntry = true) : S i = P i :=
    Option.some.inj ((local_at S K i).symm.trans
      (plain_target wide er h (local_at (fun j => (P j, false)) _ i) typedEntry))
  have along (d : Nat) (i : Fin m) (h : i ∈ anchored commonEntry commonRows d) : S i = P i := by
    induction d generalizing i with
    | zero =>
        exact entryFixed i (List.mem_filter.mp h).2
    | succ d ih =>
        have edges := Bool.or_eq_true_iff.mp (List.mem_filter.mp h).2
        rcases edges with start | step
        · exact entryFixed i start
        · obtain ⟨j, known, next⟩ := List.any_eq_true.mp step
          have typed := typedRows j
          rw [ih j known] at typed
          exact Option.some.inj ((local_at S K i).symm.trans
            (plain_target wide (rr j) next (local_at (fun j => (P j, false)) _ i) typed))
  exact funext fun i => along d i (paths i)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgFiniteSyntax
