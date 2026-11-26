module

public import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Thms
public import Silmaril.SSA.RVSDG.MLIR.Graph.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Proofs

open RVSDG (Port Tuple)
open RVSDG.MLIR.Graph (ofAssignment toAssignment)
open Silmaril.MLIR.Institution (Assignment)

variable {Data : Type} {Op : Diamond.Signature.{0, 0} Data}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Diamond.Ty Data))} {out : ValueSort Data}

theorem returns_iff_denote (m : Model.{0, 0, 0} Op) (g : Graph Op inputs sigs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) (result : sortValue m.value out) :
    g.Returns m entry result ↔ denote m g entry = result := by
  have h := RVSDG.MLIR.Graph.denote_lower (P := source Op) m.toRVSDG g.lower entry
  change Tuple.cons (F := m.toRVSDG.Val) (t := .value out) (denote m g entry) Tuple.nil =
    g.lower.run m.toRVSDG entry at h
  rw [g.lower_returns_iff m entry result, ← h]
  exact ⟨fun eq => congrArg (fun xs => Tuple.get xs Port.head) eq,
    fun eq => congrArg (fun value => Tuple.cons value Tuple.nil) eq⟩

theorem denote_eq (m : Model.{0, 0, 0} Op) (g : Graph Op inputs sigs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) :
    denote m g entry = g.denote m entry :=
  (returns_iff_denote m g entry _).mp ((g.returns_iff_denote m entry _).mpr rfl)

private theorem to_ofAssignment {F : Diamond.Ty Data → Type} (ports : List (Diamond.Ty Data))
    (env : Assignment F ports.get) : toAssignment (ofAssignment ports env) = env := by
  induction ports with
  | nil => exact funext fun i => i.elim0
  | cons _ _ ih =>
    funext i
    exact Fin.cases rfl (fun j => congrFun (ih (fun k => env k.succ)) j) i

theorem satisfaction (m : Model.{0, 0, 0} Op) {rightSigs : List (List (Diamond.Ty Data))}
    (lhs : Graph Op inputs sigs out) (rhs : Graph Op inputs rightSigs out) :
    (lowerEquation lhs rhs).Holds (model m) ↔
      ∀ entry : Tuple (Val m.value) (dataPorts inputs), lhs.denote m entry = rhs.denote m entry := by
  change (∀ env : Assignment (Val m.value) (dataPorts inputs).get, ∀ i : Fin 1,
    (lower lhs i).denote (model m) env = (lower rhs i).denote (model m) env) ↔ _
  constructor
  · intro holds entry
    exact (denote_eq m lhs entry).symm.trans
      ((holds (toAssignment entry) 0).trans (denote_eq m rhs entry))
  · intro holds env i
    rw [Fin.fin_one_eq_zero i]
    let entry : Tuple (Val m.value) (dataPorts inputs) := ofAssignment (dataPorts inputs) env
    have entry_eq : toAssignment entry = env := to_ofAssignment (dataPorts inputs) env
    rw [← entry_eq]
    exact (denote_eq m lhs entry).trans ((holds entry).trans (denote_eq m rhs entry).symm)

end Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Proofs
