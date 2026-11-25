module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms

/-! # Linked continuation congruence in the shared opt-in proof theory -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper

variable {τ : Type u} [Silmaril.TypeFormers τ] {Φ : Type v} [Silmaril.HasTy Φ τ]

theorem linkExits {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) {σ υ : Nat → Region Φ} (hs : Equivalent Γ L K σ υ) :
    Eqv Γ (r.linkExits L σ) (s.linkExits L υ) K := by
  have hprefix : List.ofFn (fun i : Fin L.length => L.get i) = L := List.ofFn_get L
  have hin : Ren L (List.ofFn (fun i : Fin L.length => L.get i) ++ K) id := by
    intro i A hi
    have hlt := (List.getElem?_eq_some_iff.mp hi).1
    simpa only [hprefix, id_eq, At, List.getElem?_append_left hlt] using hi
  have hout : Ren K (List.ofFn (fun i : Fin L.length => L.get i) ++ K)
      (fun j => L.length + j) := by
    intro j A hj
    simpa [hprefix, At, List.getElem?_append_right] using hj
  refine .cfg (fun i : Fin L.length => L.get i) ?_ (fun i => ?_)
  · simpa only [renameLabels_id] using h.renameLabels hin
  · exact (hs (show At L i (L.get i) by simp [At])).renameLabels hout

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
