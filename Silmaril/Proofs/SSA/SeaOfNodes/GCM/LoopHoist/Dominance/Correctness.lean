module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Defs

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Dominance

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Terminator)
open Silmaril.SSA.RVSDG (extend)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.MLIR.Lowering (Scope lowerCode)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance
open Loop.MLIR.CF (Program lower opcode entryScope headerScope entryTerm headerTerm)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}

private theorem lowerCode_targets {ports : List (Diamond.Ty Width)}
    {past sigs : List (List (Diamond.Ty Width))} {Γ : List Width}
    (flow : Diamond.Dataflow Loop.MLIR.CF.Op ports past sigs)
    (scope : Scope ports past Γ)
    (finish : ∀ {Δ}, Scope ports (extend past sigs) Δ → Terminator (SourceLabel carried result) [result] Δ)
    (targets : EdgeSlot → Option (Target (SourceLabel carried result)))
    (agrees : ∀ {Δ} (names : Scope ports (extend past sigs) Δ),
      shape.targetAt (finish names) = targets) :
    (shape.ofBlock (lowerCode opcode flow scope finish)).target = targets := by
  induction flow generalizing Γ with
  | nil => exact agrees scope
  | cons op operands rest ih =>
    exact ih (scope.pushValue _) finish agrees

theorem lower_targets (g : Program Input carried result entrySigs headerSigs)
    (block : BlockId (SourceLabel carried result)) :
    (shape (lower g) block).target = expectedTarget block := by
  cases block with
  | none =>
    exact lowerCode_targets g.preheader (entryScope Input) (entryTerm g) _
      (fun _ => funext (fun slot => by cases slot <;> rfl))
  | some target =>
    cases target with
    | mk _ label =>
      cases label with
      | header =>
        exact lowerCode_targets g.header (headerScope Input carried) (headerTerm g) _
          (fun _ => funext (fun slot => by cases slot <;> rfl))
      | exit => exact funext (fun slot => by cases slot <;> rfl)

private theorem stage_injective {a b : BlockId (SourceLabel carried result)}
    (same : stage a = stage b) : a = b := by
  rcases a with _ | ⟨_, a⟩ <;> rcases b with _ | ⟨_, b⟩
  · rfl
  · cases b <;> simp [stage] at same
  · cases a <;> simp [stage] at same
  · cases a <;> cases b <;> simp_all [stage]

theorem address_injective {a b : BlockId (SourceLabel carried result)}
    (same : address a = address b) : a = b :=
  stage_injective (by simpa [address] using congrArg List.length same)

private theorem edge_bounds {src : BlockId (SourceLabel carried result)}
    {dst : Target (SourceLabel carried result)} (slot : EdgeSlot)
    (edge : (shape (lower g) src).target slot = some dst) :
    stage src ≤ stage (some dst) ∧ stage (some dst) ≤ stage src + 1 := by
  rw [lower_targets] at edge
  rcases src with _ | ⟨_, label⟩
  · cases slot <;> cases edge <;> simp [stage]
  · cases label <;> cases slot <;> cases edge <;> simp [stage]

private theorem path_visits {a b : BlockId (SourceLabel carried result)} {past}
    (path : EntryPath (lower g) b past) : a ∈ past ↔ stage a ≤ stage b := by
  induction path with
  | entry =>
    constructor
    · intro member
      simpa only [List.mem_singleton.mp member] using Nat.le_refl (stage none)
    · intro bound
      exact List.mem_singleton.mpr (stage_injective (Nat.eq_zero_of_le_zero bound))
  | @step src prior dst previous slot edge ih =>
    have bounds := edge_bounds slot edge
    constructor
    · intro member
      rcases List.mem_cons.mp member with same | earlier
      · exact same.symm ▸ Nat.le_refl _
      · exact Nat.le_trans (ih.mp earlier) bounds.1
    · intro bound
      by_cases same : stage a = stage (some dst)
      · exact List.mem_cons.mpr (.inl (stage_injective same))
      · exact List.mem_cons_of_mem _ (ih.mpr (by omega))

theorem reachable (g : Program Input carried result entrySigs headerSigs)
    (block : BlockId (SourceLabel carried result)) : Reachable (lower g) block := by
  have header : EntryPath (lower g) headerId [headerId, none] :=
    .step .entry .jump (by rw [lower_targets]; rfl)
  rcases block with _ | ⟨_, label⟩
  · exact ⟨_, .entry⟩
  cases label
  · exact ⟨_, header⟩
  · exact ⟨_, .step header .onFalse (by rw [lower_targets]; rfl)⟩

theorem prefix_iff_dominates (g : Program Input carried result entrySigs headerSigs)
    (a b : BlockId (SourceLabel carried result)) :
    List.IsPrefix (address a) (address b) ↔ Dominates (lower g) a b := by
  have prefix_iff : List.IsPrefix (address a) (address b) ↔ stage a ≤ stage b := by
    simp [address, List.prefix_replicate_iff]
  refine prefix_iff.trans ⟨?_, ?_⟩
  · intro order past path
    exact (path_visits path).mpr order
  · intro dominates
    obtain ⟨past, path⟩ := reachable g b
    exact (path_visits path).mp (dominates past path)

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Dominance
