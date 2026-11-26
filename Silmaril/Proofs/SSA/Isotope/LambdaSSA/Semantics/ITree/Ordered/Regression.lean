module

import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Thms

/-! # A visible packed comparison after a non-injective primitive relabelling -/

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.Regression

open Silmaril.Elgot.ITree
open Silmaril.Isotope.LambdaSSA.Semantics (Env)
open Silmaril.Isotope.LambdaSSA.FiniteCFG (packedExecutionRegion packedExecution_tree packedTreeOutput)
open Silmaril.Isotope.Morphism (SignatureMap)

private abbrev SortName := ULift.{1} Unit
private instance : AtomValues SortName := ⟨fun _ => ULift Unit⟩
attribute [local instance] typeModel

private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))

private inductive Opcode
  | quiet
  | ping
  | alias

private inductive Event : Type → Type
  | call (op : Opcode) : Event Nat

private instance : HasTy Opcode (Ty SortName) := ⟨fun _ => .unit, fun _ => .unit⟩
private instance : HasEff Opcode Bool := ⟨fun _ => true⟩

private def action {X : Type 1} (op : Opcode) (reply : Nat → Tree Event X) : Tree Event X :=
  match op with
  | .quiet => diverge
  | .ping | .alias => vis (.call op) reply

private def model : Model (κ := SortName) Event Opcode where
  instructions :=
    { denote := fun op _ => action op (fun _ => pure PUnit.unit)
      denotePure := fun _ h => Bool.noConfusion h
      denote_pure := fun _ h => Bool.noConfusion h }
  raw := fun op _ => action op (fun _ => pure .unit)
  compatible := by
    dsimp only
    intro op input
    cases op <;> simp [action, diverge_bind, vis_bind, -bind_pure_comp]
    all_goals
      funext reply
      change (pure .unit : Tree Event (Value Runtime)) =
        ((pure PUnit.unit : Tree Event PUnit.{2}) >>= fun _ => pure .unit)
      rw [pure_bind]

private def rename : SignatureMap Opcode Opcode (Ty SortName) (Ty SortName) Bool Bool where
  instr
    | .quiet => .quiet
    | .ping | .alias => .alias
  ty := id
  eff := id
  source _ := rfl
  target _ := rfl
  effect _ := rfl

private def graph (op : Opcode) : FiniteCFG Opcode 0 1 0 :=
  ⟨.br 0 (.op op .unit), Fin.elim0⟩

private theorem graph_typed (op : Opcode) :
    (graph op).HasType .nil (fun _ => Ty.unit) (fun _ => Ty.unit (α := SortName)) :=
  ⟨.br (.op .unit), fun i => Fin.elim0 i⟩

private def ambient : Env Runtime := fun _ => .unit

private theorem rename_types : rename.ty = id := rfl
private theorem rename_bottom : rename.eff ⊥ = ⊥ := rfl

private def reduct := model.reduct rename rename_types rename_bottom

private theorem packed_tree (op : Opcode) :
    region reduct.raw ambient (packedExecutionRegion (graph_typed op)) =
      action (rename.instr op) (fun _ => pure (0, .inl .unit)) := by
  rw [packedExecution_tree]
  cases op <;> simp [reduct, Model.reduct, model, rename, action, graph, FiniteCFG.erase,
    Flat.erase, Morphism.CaseSSA.erase, region, term, splitTransfer, packedTreeOutput,
    Region.packedExitValue, diverge_bind, vis_bind, pure_bind, -bind_pure_comp]

private abbrev quiet := Program.ofCFG (graph_typed .quiet)
private abbrev ping := Program.ofCFG (graph_typed .ping)

-- The image primitive is used in the original event family, and the two
-- programs have distinct trace orders after packing.
example : model.Satisfies (quiet.map rename rename_types) (ping.map rename rename_types) ∧
    ¬ model.Satisfies (ping.map rename rename_types) (quiet.map rename rename_types) := by
  rw [satisfies_map_iff model rename rename_types rename_bottom,
    satisfies_map_iff model rename rename_types rename_bottom]
  change reduct.Satisfies quiet ping ∧ ¬ reduct.Satisfies ping quiet
  rw [satisfies_ofCFG_iff reduct (graph_typed .quiet) (graph_typed .ping) ambient,
    satisfies_ofCFG_iff reduct (graph_typed .ping) (graph_typed .quiet) ambient,
    packed_tree, packed_tree]
  change TraceLE (diverge : Tree Event (Transfer Runtime)) (vis (.call .alias) _) ∧
    ¬ TraceLE (vis (.call .alias) _) (diverge : Tree Event (Transfer Runtime))
  refine ⟨traceLE_diverge _, fun h => ?_⟩
  have pending := h (.request (.call .alias)) (hasTrace_vis_request _ _)
  simp [hasTrace_diverge_iff] at pending

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.Regression
