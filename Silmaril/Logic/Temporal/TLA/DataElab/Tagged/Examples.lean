module

import Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Thms
meta import Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Thms
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs

/-! Tagged regressions for the finite interval and arithmetic used by HourClock. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Examples

open Resolution Data.Tagged

private meta def standardId (i : Nat) : BindingId := .declared ⟨"attested", [.member i]⟩
private meta def hourId : BindingId := .declared ⟨"clock", [.unit 0, .member 0]⟩

private meta def table : BindingId → Option NumericPrimitive
  | .declared ⟨"attested", [.member 0]⟩ => some .interval
  | .declared ⟨"attested", [.member 1]⟩ => some .modulo
  | .declared ⟨"attested", [.member 2]⟩ => some .add
  | .declared ⟨"attested", [.member 3]⟩ => some .naturals
  | .declared ⟨"clock", [.unit 0]⟩ => some .add
  | _ => none

private meta def profile : ModuleInput :=
  .signature "Naturals" []
    [.operator (.symbol .infix "..") [.expression, .expression],
     .operator (.symbol .infix "%") [.expression, .expression],
     .operator (.symbol .infix "+") [.expression, .expression],
     .constant (.ident "Nat" 0)]

private meta def lowerSource (text : String) (imports : ImportMap) (dependencies : Registry)
    (unit : Nat) : Except String (Term (numericSignature table)) := do
  let source ← (Surface.Parser.parseModule text).mapError reprStr
  let registry ← (Resolution.resolve (("clock", .parsed source imports) :: dependencies)
    "clock").mapError reprStr
  let checked ← (lowerDefinition registry (numericSignature table) 20
    (.declared ⟨"clock", [.unit unit]⟩)).mapError reprStr
  return checked.term

private meta def clockText := r#"---- MODULE ClockSlice ----
EXTENDS Naturals
VARIABLE hr
Initial == hr \in (1 .. 12)
NextValue == (hr % 12) + 1
InNaturals == hr \in Nat
====
"#

private meta def lowerClock (unit : Nat) : Except String (Term (numericSignature table)) :=
  lowerSource clockText [("Naturals", "attested")] [("attested", profile)] unit

#guard match lowerClock 1 with
  | .ok (.mem false (.flexible id) (.external key 2 _ [.numeral 1, .numeral 12])) =>
    id = hourId ∧ key = standardId 0
  | _ => false

#guard match lowerClock 2 with
  | .ok (.external plus 2 _ [.external mod 2 _ [.flexible id, .numeral 12], .numeral 1]) =>
    id = hourId ∧ plus = standardId 2 ∧ mod = standardId 1
  | _ => false

#guard match lowerClock 3 with
  | .ok (.mem false (.flexible id) (.external key 0 _ [])) =>
    id = hourId ∧ key = standardId 3
  | _ => false

-- The external table includes the exact ID of the parsed operator.
#guard match lowerSource "---- MODULE Parsed ----\na + b == a\nOut == 1 + 7\n====" [] [] 1 with
  | .ok (.numeral 1) => true
  | _ => false

private theorem foundInterval : table (standardId 0) = some .interval := by
  simp [table, standardId]

private theorem foundModulo : table (standardId 1) = some .modulo := by
  simp [table, standardId]

private theorem foundAdd : table (standardId 2) = some .add := by
  simp [table, standardId]

private noncomputable def initialTerm : Term (numericSignature table) :=
  .mem false (.flexible hourId) (.external (standardId 0) 2
    (by simp [numericSignature, foundInterval, NumericPrimitive.arity]) [.numeral 1, .numeral 12])

private noncomputable def nextValueTerm : Term (numericSignature table) :=
  .external (standardId 2) 2 (by simp [numericSignature, foundAdd, NumericPrimitive.arity])
    [.external (standardId 1) 2 (by simp [numericSignature, foundModulo, NumericPrimitive.arity])
      [.flexible hourId, .numeral 12], .numeral 1]

universe u
variable (policy : Policy.{u})

private noncomputable def evaluate (term : Term (numericSignature table)) (hour : Int) : Value.{u} :=
  let readHour := fun _ => Value.integer hour
  term.eval policy.operations policy.booleans (policy.external table) ⟨readHour, readHour⟩
    (fun _ => policy.operations.enum [])

private theorem initial_iff (hour : Int) :
    policy.booleans.holds (evaluate policy initialTerm hour) ↔ 1 ≤ hour ∧ hour ≤ 12 := by
  simp only [evaluate, initialTerm, Term.eval, Term.evalList, Bool.false_eq_true, ite_false,
    policy.numeral_eq, Booleans.holds_ofProp, policy.mem_value]
  rw [policy.external_apply table foundInterval]
  simp [SetData.integer_mem_intRange]

private theorem next_value_eq (hour : Int) :
    evaluate policy nextValueTerm hour = Value.integer (hour % 12 + 1) := by
  simp only [evaluate, nextValueTerm, Term.eval, Term.evalList, policy.numeral_eq]
  rw [policy.external_apply table foundAdd, policy.external_apply table foundModulo]
  simp [Value.modulo_integer]

example (x : Value.{u}) (n : Int) : ¬ policy.operations.mem x (Value.integer n) :=
  policy.not_mem_of_asSet_none (Value.asSet_integer n)

example (n : Int) (predicate : Value.{u} → Prop) :
    policy.operations.sep (Value.integer n) predicate =
      policy.invalidSet .separation (Value.integer n) :=
  policy.sep_of_asSet_none (Value.asSet_integer n) predicate

example (n : Int) (f : Value.{u} → Value.{u}) :
    policy.operations.image (Value.integer n) f = policy.invalidSet .image (Value.integer n) :=
  policy.image_of_asSet_none (Value.asSet_integer n) f

example (n : Int) (predicate : Value.{u} → Prop) :
    policy.operations.choice.choose
      (fun x => policy.operations.mem x (Value.integer n) ∧ predicate x) =
      policy.choice.noWitness :=
  policy.choose_of_asSet_none (Value.asSet_integer n) predicate

example (n : Int) :
    (policy.primitive .modulo).apply [Value.integer n, Value.integer 0] =
      policy.numeric .modulo [Value.integer n, Value.integer 0] := by
  rw [policy.modulo_apply, Value.modulo_nonpositive _ _ _ (Int.le_refl _)]

end Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Examples
