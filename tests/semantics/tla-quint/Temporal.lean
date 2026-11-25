module

import all Silmaril.Logic.Temporal.TLA.Elaborator.Defs
import all Silmaril.Logic.Temporal.TLA.Defs
import Silmaril.Logic.Temporal.TLA.Elaborator.Thms
import Silmaril.Logic.Temporal.TLA.Import.Defs
meta import Silmaril.Logic.Temporal.TLA.Import.Defs
meta import Silmaril.ProofFormats.TLA.SurfaceSExp.Defs

open Silmaril.Logic.Temporal.TLA
open Silmaril.ProofFormats.TLA
open Elaborator (Signature Observation TemporalFormula)
open Surface (Expr ModuleUnit)

private def signature : Signature := [("ready", .bool), ("done", .bool)]
private def source : String := include_str "Intermittent.tla"

private def ref (name : String) : Expr := .ref (.operator (.ident name)) [] []
private def bin (op : String) (left right : Expr) : Expr := .infix (.symbol op) left right
private def defn (name : String) (body : Expr) : ModuleUnit :=
  .definition (.operator .ordinary (.ident name []) body)

private def tree : Surface.Module :=
  let bracket (observe : Expr) := Expr.prefix .always (.action .square (ref "Next") observe)
  let weak := Expr.fairness .weak (ref "done") (ref "Next")
  let vars := Expr.tuple [ref "ready", ref "done"]
  ⟨"Intermittent", [],
    [.variables ["ready", "done"],
     defn "Init" (bin "/\\" (ref "ready") (.prefix .negation (ref "done"))),
     defn "Next" (bin "/\\" (ref "ready") (bin "=" (.postfix .prime (ref "done")) (ref "TRUE"))),
     defn "vars" vars,
     defn "Safe" (.junction .conjunction [ref "Init", bracket (ref "done")]),
     defn "Weak" (bin "/\\" (ref "Safe") weak),
     defn "Strong" (bin "/\\" (ref "Safe") (.fairness .strong (ref "done") (ref "Next"))),
     defn "Full" (bin "/\\" (ref "Init") (bracket (ref "vars"))),
     defn "Both" (bin "/\\" (bin "/\\" (ref "Full") weak) (.fairness .strong vars (ref "Next")))]⟩

-- Compare the complete parsed tree. The partial parser runs in the executable
-- check, and the kernel proves the behavior claims for the same tree below.
#guard match Surface.Parser.parseModule source with
  | .ok parsed => SurfaceSExp.encodeModuleText parsed == SurfaceSExp.encodeModuleText tree
  | .error _ => false

private def checked := Elaborator.elaborate [] signature tree
private def ρ := signature.noRigid

private def raw : Kernel.StepPredicate signature.scope :=
  (checked >>= (·.stepPredicate "Next")).toOption.get (by decide)

private def safe : TemporalFormula signature.scope :=
  (checked >>= (·.temporalFormula "Safe")).toOption.get (by decide)
private def weak : TemporalFormula signature.scope :=
  (checked >>= (·.temporalFormula "Weak")).toOption.get (by decide)
private def strong : TemporalFormula signature.scope :=
  (checked >>= (·.temporalFormula "Strong")).toOption.get (by decide)
private def full : TemporalFormula signature.scope :=
  (checked >>= (·.temporalFormula "Full")).toOption.get (by decide)

private def state (ready done : Bool) : Kernel.State signature.scope
  | .int, _ => (0 : Int)
  | .bool, name => if name.val == "ready" then ready else done

private def run : Behavior (Kernel.State signature.scope) :=
  fun n => state (decide (n % 2 = 0)) false

#guard match Import.importModule ⟨signature, [], "Init", "Next"⟩ source with
  | .ok imported => imported.initial.check ρ (run 0) &&
    !imported.step.check ρ (run 0, run 1) && imported.step.check ρ (run 0, state false true)
  | .error _ => false

-- The source bracket on `done` permits the run. A full-state bracket disallows
-- its first transition because `ready` changes and the raw step requires `done'`.
private theorem safe_run : (safe.toFormula ρ).Sat run :=
  ⟨⟨rfl, Bool.noConfusion⟩, fun _ _ => Or.inr rfl⟩

example : ¬ (full.toFormula ρ).Sat run := by
  rintro ⟨_, steps⟩
  rcases steps 0 (Nat.zero_le 0) with ⟨_, done⟩ | equal
  · exact Bool.noConfusion (show false = true from done)
  · change [Sum.inr (α := Int) false, Sum.inr false] = [.inr true, .inr false] at equal
    simp at equal

private def observeDone : Observation signature.scope :=
  let done := Kernel.Term.flex (Γ := signature.scope) (a := .bool) ⟨"done", rfl⟩
  Kernel.Term.enumeration [Kernel.Term.map Sum.inr (Kernel.Predicate.ofBool done).check]

-- The action can finish at each even instant. It is disabled at odd instants,
-- and the behavior never finishes, so WF holds and SF fails.
example : (weak.toFormula ρ).Sat run ∧ ¬ (strong.toFormula ρ).Sat run := by
  have hWeak : ((TemporalFormula.weakFair raw observeDone).toFormula ρ).Sat run := by
    apply (TemporalFormula.sat_weakFair raw observeDone ρ run).mpr
    rintro ⟨i, continuous⟩
    obtain ⟨_, ⟨ready, _⟩, _⟩ := continuous (2 * i + 1) (by omega)
    change decide ((2 * i + 1) % 2 = 0) = true at ready
    have := of_decide_eq_true ready
    omega
  have hStrong : ¬ ((TemporalFormula.strongFair raw observeDone).toFormula ρ).Sat run := by
    intro fair
    have recurrent (i : Nat) : ∃ j, i ≤ j ∧ ((raw.toAction ρ).angle (observeDone ρ)).enabled (run j) := by
      refine ⟨2 * i, by omega, state false true, ⟨?_, rfl⟩, ?_⟩
      · change decide ((2 * i) % 2 = 0) = true
        exact decide_eq_true (by omega)
      · change [Sum.inr (α := Int) true] ≠ [.inr false]
        decide
    obtain ⟨_, _, ⟨_, done⟩, _⟩ := (TemporalFormula.sat_strongFair raw observeDone ρ run).mp fair recurrent 0
    exact Bool.noConfusion (show false = true from done)
  exact ⟨⟨safe_run, hWeak⟩, fun h => hStrong h.2⟩

-- Inspect the source-selected clauses and their independent observations.
#guard match Import.importTemporal signature [] "Both" source with
  | .ok (.conj (.conj (.conj (.state _) (.alwaysBracket _ fullObs)) (.weakFair _ weakObs))
      (.strongFair _ strongObs)) =>
    fullObs ρ (run 0) == [.inr true, .inr false] &&
    weakObs ρ (run 0) == [.inr false] && strongObs ρ (run 0) == fullObs ρ (run 0)
  | _ => false

private def mixed : Signature := [("flag", .bool), ("n", .int)]
private def mixedState : Kernel.State mixed.scope
  | .int, _ => (3 : Int)
  | .bool, _ => true

#guard match Import.importTemporal mixed [] "Spec" "---- MODULE Mixed ----\n\
    VARIABLES n, flag\nNext == n' = 0\nvars == <<n, flag>>\nSpec == [][Next]_vars\n====" with
  | .ok (.alwaysBracket _ obs) => obs mixed.noRigid mixedState == [.inl 3, .inr true]
  | _ => false

private def rejected (body : String) (expected : Elaborator.Diagnostic) : Bool :=
  let extended := source.replace "====" s!"Rejected == {body}\n===="
  match Import.importTemporal signature [] "Safe" extended with
  | .error (.elaborate (.inDefinition "Rejected" actual)) => decide (actual = expected)
  | _ => false

#guard rejected "[][Next]_missing" (.unknownName "missing")
#guard rejected "[][Next]_(done')" .actionInObservation
#guard rejected "SF_<<ready, done'>>(Next)" .actionInObservation
#guard rejected "WF_<<>>(Next)" (.unsupportedExpression "empty observation tuple")
#guard rejected "[][Next]_Safe" .temporalInScalar
#guard rejected "[][Next]_<<vars, done>>" .tupleInScalar
#guard rejected "[][Next]_vars(TRUE)" (.arityMismatch "vars" 0 1)
#guard rejected "WF_done(Missing)" (.unknownName "Missing")
#guard rejected "WF_done(Next(TRUE))" (.arityMismatch "Next" 0 1)
#guard rejected "SF_done(0)" (.typeMismatch .bool .int)
#guard rejected "WF_done(Weak)" .temporalInScalar
#guard rejected "Next /\\ Safe" .actionInTemporal
#guard rejected "vars = vars" .tupleInScalar
#guard rejected "[Next]_done" (.unsupportedExpression "action bracket")
#guard rejected "[]Next" (.unsupportedExpression "scalar state/action fragment")
#guard rejected "~Weak" .temporalInScalar
#guard rejected "Weak \\/ Strong" .temporalInScalar

#guard match Import.importTemporal signature [] "Next" source with
  | .error (.temporal "Next" (.expectedTemporal "Next")) => true
  | _ => false

#guard match Import.importModule ⟨signature, [], "Init", "Safe"⟩ source with
  | .error (.step "Safe" .temporalInScalar) => true
  | _ => false
