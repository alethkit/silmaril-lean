module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.MultiNested.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmissionSyntax
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgFiniteSyntax
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Check.Thms

/-! # Selected rows and typed transfers in an accepted table -/

public section

universe v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMultiSyntax

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.MultiNested
open Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite (branchesTo)

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

private theorem row_checked {form : Bool} {A : Ty Empty} {out : RouteLayout Empty}
    {r : Region Φ} {p : RowPlan Φ} (ok : checkRow? form A out r = some p) :
    p.Valid A out r form := by
  cases form with
  | false =>
      obtain ⟨common, route, rfl⟩ := Option.map_eq_some_iff.mp ok
      exact .ordinary route
  | true =>
      simp only [checkRow?, Option.bind_eq_some_iff] at ok
      obtain ⟨selected, choice, rest⟩ := ok
      split at rest <;> try contradiction
      rename_i blocks
      obtain ⟨common, route, rfl⟩ := Option.map_eq_some_iff.mp rest
      have eq : (Region.cfg (.br 0 (.var 0)) 1 blocks : Region Φ) = inner (blocks 0) := by
        congr 1
        funext i
        cases Subsingleton.elim i (0 : Fin 1)
        rfl
      exact .nested (eq ▸ NestedCfgAdmissionSyntax.selected choice) route

theorem checked {m n : Nat} {keep : Fin m ↪ Fin n} {P : Fin m → Ty Empty} {forms : Fin m → Bool}
    {r : Region Φ} {L : LCtx (Ty Empty)} {p : Plan Φ m n}
    (ok : check? keep P forms r L = some p) : p.Valid keep P forms r L := by
  simp only [check?, Option.bind_eq_some_iff] at ok
  obtain ⟨outer, ho, entry, he, rows, hr, ok⟩ := ok
  split at ok <;> try contradiction
  rename_i all
  cases Option.some.inj ok
  exact ⟨CfgRestriction.check?_sound ho, he, fun i => row_checked (Region.checkFamily_some hr i),
    fun i => by simpa using List.all_eq_true.mp all i (List.mem_finRange _)⟩

@[expose] def Fits (A : Ty Empty) (tag : Bool) (T : Ty Empty) : Prop :=
  if tag then ∃ D, T = .coprod A D else T = A

theorem target {m : Nat} {P S : Fin m → Ty Empty} {forms : Fin m → Bool} {L : LCtx (Ty Empty)}
    (locals : RouteLayout Empty) {Γ : VCtx (Ty Empty)} {r common : Region Φ}
    (route : r.checkRoutes? (locals ++ layout P forms L) Γ = some common)
    (typed : r.HasType Γ (locals.map Prod.fst ++ List.ofFn S ++ L)) (i : Fin m)
    (edge : branchesTo (locals.length + i.val) common = true) : Fits (P i) (forms i) (S i) := by
  have hit : (locals ++ layout P forms L)[locals.length + i.val]? = some (P i, forms i) := by
    simp [layout, List.getElem?_append_right, List.getElem?_append_left, i.isLt]
  have actual : (locals.map Prod.fst ++ List.ofFn S ++ L)[locals.length + i.val]? = some (S i) := by
    simp [List.getElem?_append_right, List.getElem?_append_left, i.isLt]
  have determined := NestedCfgFiniteSyntax.route_target true (forms i) route edge hit typed
  cases h : forms i with
  | false =>
      have atType : At (locals.map Prod.fst ++ List.ofFn S ++ L) (locals.length + i.val) (P i) := by
        simpa only [h, Bool.and_false, Bool.false_eq_true, ite_false] using determined
      simpa only [Fits, h, Bool.false_eq_true, ite_false] using Option.some.inj (actual.symm.trans atType)
  | true =>
      have found : ∃ D, At (locals.map Prod.fst ++ List.ofFn S ++ L) (locals.length + i.val) (.coprod (P i) D) := by
        simpa only [h, Bool.and_self, ite_true] using determined
      obtain ⟨D, atType⟩ := found
      simp only [Fits, ite_true]
      exact ⟨D, Option.some.inj (actual.symm.trans atType)⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMultiSyntax
