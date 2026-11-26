module

import all Silmaril.Logic.Temporal.TLA.Elaborator.Defs
import all Silmaril.Logic.Temporal.TLA.Defs
import Silmaril.Logic.Temporal.TLA.Elaborator.Thms
import Silmaril.Logic.Temporal.TLA.Import.Defs
meta import Silmaril.Logic.Temporal.TLA.Import.Defs
meta import Silmaril.ProofFormats.TLA.SurfaceSExp.Defs

open Silmaril.Logic.Temporal.TLA
open Silmaril.ProofFormats.TLA
open Elaborator (TemporalFormula)
open Surface (Expr ModuleUnit)

private def profile : Import.Profile := .quintApalache0624 [("phase", .int)]
private def source : String := include_str "ServiceCycle.tla"

private def ref (name : String) : Expr := .ref (.operator (.ident name)) [] []
private def bin (op : String) (left right : Expr) : Expr := .infix (.symbol op) left right
private def defn (name : String) (body : Expr) : ModuleUnit :=
  .definition (.operator .ordinary (.ident name []) body)

private def tree : Surface.Module :=
  let phase := ref "phase"
  let atPhase (n : Nat) := bin "=" phase (.literal (.natural n))
  let setPhase (n : Nat) := bin ":=" (.postfix .prime phase) (.literal (.natural n))
  let branch (n m : Nat) := bin "/\\" (atPhase n) (setPhase m)
  let step := bin "\\/" (bin "\\/" (bin "\\/" (branch 0 1) (branch 1 2))
    (bin "/\\" (bin "\\/" (atPhase 2) (atPhase 3)) (setPhase 1))) (ref "service")
  let safe := bin "/\\" (ref "atStart") (.prefix .always (.action .square (ref "step") phase))
  ⟨"ServiceCycle", ["Integers", "Sequences", "FiniteSets", "TLC", "Apalache", "Variants"],
    [.variables ["phase"], defn "init" (atPhase 0), defn "service" (branch 1 3),
      defn "atStart" (atPhase 0), defn "step" step, defn "q_init" (ref "init"),
      defn "safe" safe, defn "q_step" (ref "step"),
      defn "weak" (bin "/\\" (ref "safe") (.fairness .weak phase (ref "service"))),
      defn "strong" (bin "/\\" (ref "safe") (.fairness .strong phase (ref "service")))]⟩

-- Match the entire parser result to the tree on which the kernel proofs operate.
#guard match Surface.Parser.parseModule source with
  | .ok parsed => SurfaceSExp.encodeModuleText parsed == SurfaceSExp.encodeModuleText tree
  | .error _ => false

#guard ["safe", "weak", "strong"].all fun name =>
  (Import.importTemporal profile.signature profile.libraries name source).isOk

private def checked := Elaborator.elaborate profile.libraries profile.signature tree
private def ρ := profile.signature.noRigid
private abbrev PhaseState := Kernel.State profile.signature.scope

private def state (phase : Int) : PhaseState
  | .int, _ => phase
  | .bool, _ => false

private def phaseOf (s : PhaseState) : Int := s .int ⟨"phase", rfl⟩

private def step : Kernel.StepPredicate profile.signature.scope :=
  (checked >>= (·.stepPredicate "q_step")).toOption.get (by decide)
private def service : Kernel.StepPredicate profile.signature.scope :=
  (checked >>= (·.stepPredicate "service")).toOption.get (by decide)
private def observe : Elaborator.Observation profile.signature.scope :=
  let phase := Kernel.Term.flex (Γ := profile.signature.scope) (a := .int) ⟨"phase", rfl⟩
  Kernel.Term.enumeration [Kernel.Term.map Sum.inl phase]

private def safe : TemporalFormula profile.signature.scope :=
  (checked >>= (·.temporalFormula "safe")).toOption.get (by decide)
private def weak : TemporalFormula profile.signature.scope :=
  (checked >>= (·.temporalFormula "weak")).toOption.get (by decide)
private def strong : TemporalFormula profile.signature.scope :=
  (checked >>= (·.temporalFormula "strong")).toOption.get (by decide)

-- Reference semantics from the Quint branches and the documented temporal operators.
private def edge (a b : Int) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨
    (a = 3 ∧ b = 1) ∨ (a = 1 ∧ b = 3)

private def safeRef (run : Behavior Int) : Prop :=
  run 0 = 0 ∧ ∀ i, edge (run i) (run (i + 1)) ∨ run (i + 1) = run i

private def recurringService (run : Behavior Int) : Prop :=
  ∀ i, ∃ j, i ≤ j ∧ run j = 1 ∧ run (j + 1) = 3

private theorem step_iff (a b : Int) : (step.toAction ρ) (state a) (state b) ↔ edge a b := by
  change (((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)) ∨ ((a = 2 ∨ a = 3) ∧ b = 1)) ∨
    (a = 1 ∧ b = 3) ↔ edge a b
  simp only [edge, or_and_right, or_assoc]

private theorem visible_iff (s t : PhaseState) :
    (service.toAction ρ).angle (observe ρ) s t ↔ phaseOf s = 1 ∧ phaseOf t = 3 := by
  change (phaseOf s = 1 ∧ phaseOf t = 3) ∧
    [Sum.inl (β := Bool) (phaseOf t)] ≠ [.inl (phaseOf s)] ↔ _
  exact ⟨And.left, fun ⟨h, k⟩ => ⟨⟨h, k⟩, by simp [h, k]⟩⟩

private theorem enabled_iff (s : PhaseState) :
    ((service.toAction ρ).angle (observe ρ)).enabled s ↔ phaseOf s = 1 := by
  unfold Action.enabled
  simp only [visible_iff]
  exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨state 3, h, rfl⟩⟩

private theorem safe_iff (run : Behavior Int) :
    (safe.toFormula ρ).Sat (run.map state) ↔ safeRef run := by
  change (run 0 = 0 ∧
    ((TemporalFormula.alwaysBracket step observe).toFormula ρ).Sat (run.map state)) ↔ _
  rw [TemporalFormula.sat_alwaysBracket]
  simp only [safeRef, Behavior.map, step_iff]
  change (run 0 = 0 ∧ ∀ i, edge (run i) (run (i + 1)) ∨
    [Sum.inl (β := Bool) (run (i + 1))] = [.inl (run i)]) ↔ _
  simp only [List.cons.injEq, Sum.inl.injEq, and_true]

private theorem weak_iff (run : Behavior Int) :
    (weak.toFormula ρ).Sat (run.map state) ↔ safeRef run ∧
      ((∃ i, ∀ j, i ≤ j → run j = 1) → recurringService run) := by
  change (safe.toFormula ρ).Sat (run.map state) ∧
    ((TemporalFormula.weakFair service observe).toFormula ρ).Sat (run.map state) ↔ _
  rw [safe_iff, TemporalFormula.sat_weakFair]
  simp only [enabled_iff, visible_iff, recurringService, Behavior.map, phaseOf, state]

private theorem strong_iff (run : Behavior Int) :
    (strong.toFormula ρ).Sat (run.map state) ↔ safeRef run ∧
      ((∀ i, ∃ j, i ≤ j ∧ run j = 1) → recurringService run) := by
  change (safe.toFormula ρ).Sat (run.map state) ∧
    ((TemporalFormula.strongFair service observe).toFormula ρ).Sat (run.map state) ↔ _
  rw [safe_iff, TemporalFormula.sat_strongFair]
  simp only [enabled_iff, visible_iff, recurringService, Behavior.map, phaseOf, state]

-- One state of prefix followed by the two-state cycle (1, target), forever.
private def lasso (target : Int) : Behavior Int
  | 0 => 0
  | n + 1 => if n % 2 = 0 then 1 else target

private theorem lasso_safe (target : Int) (h : target = 2 ∨ target = 3) : safeRef (lasso target) := by
  refine ⟨rfl, fun i => Or.inl ?_⟩
  cases i with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ n =>
    rcases h with rfl | rfl <;>
      by_cases even : n % 2 = 0 <;>
      simp [edge, lasso, even, show (n + 1) % 2 = 0 ↔ ¬ n % 2 = 0 by omega]

private theorem lasso_pair (target : Int) (i : Nat) :
    lasso target (2 * i + 1) = 1 ∧ lasso target (2 * i + 2) = target := by
  have even : 2 * i % 2 = 0 := by omega
  simp [lasso, even]

private theorem service_lasso :
    (weak.toFormula ρ).Sat ((lasso 3).map state) ∧
    (strong.toFormula ρ).Sat ((lasso 3).map state) := by
  have occurs : recurringService (lasso 3) := fun i => ⟨2 * i + 1, by omega, lasso_pair 3 i⟩
  exact ⟨(weak_iff _).mpr ⟨lasso_safe 3 (Or.inr rfl), fun _ => occurs⟩,
    (strong_iff _).mpr ⟨lasso_safe 3 (Or.inr rfl), fun _ => occurs⟩⟩

private theorem bypass_lasso :
    (weak.toFormula ρ).Sat ((lasso 2).map state) ∧
    ¬ (strong.toFormula ρ).Sat ((lasso 2).map state) := by
  constructor
  · refine (weak_iff _).mpr ⟨lasso_safe 2 (Or.inl rfl), ?_⟩
    rintro ⟨i, alwaysReady⟩
    have := alwaysReady (2 * i + 2) (by omega)
    rw [(lasso_pair 2 i).2] at this
    omega
  · intro fair
    have ready : ∀ i, ∃ j, i ≤ j ∧ lasso 2 j = 1 :=
      fun i => ⟨2 * i + 1, by omega, (lasso_pair 2 i).1⟩
    obtain ⟨j, _, _, serviced⟩ := (strong_iff _).mp fair |>.2 ready 0
    simp [lasso] at serviced
    split at serviced <;> omega
