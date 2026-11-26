module

public import Silmaril.Languages.Python.Core.Module.SeededCall.Defs
import Silmaril.Proofs.Languages.Python.Core.Module.SeededCall.Correspondence

public section

namespace Silmaril.Languages.Python.Core.Module.SeededCall

theorem Namespace.module_precedes (space : Namespace) {name : String} {value : Value}
    (found : lookupBinding space.moduleGlobals name = some value) : space.lookupGlobal name = some value := by
  simp [Namespace.lookupGlobal, found]

theorem Namespace.builtin_fallback (space : Namespace) {name : String}
    (absent : lookupBinding space.moduleGlobals name = none) :
    space.lookupGlobal name = lookupBinding space.builtins name := by
  simp [Namespace.lookupGlobal, absent]

theorem Namespace.bind_preserves_builtins (space : Namespace) (name : String) (value : Value) :
    (space.bindGlobal name value).builtins = space.builtins := rfl

theorem Operand.eval_local {slots : Nat} (space : Namespace) (locals : Locals slots) (slot : Fin slots) :
    (Operand.local slot).eval space locals =
      (locals.get slot).elim (.error (.raised (.runtime (.unboundLocal slot.val)))) .ok := rfl

theorem Expectation.delivers_iff {expectation : Expectation} {input output : Result} :
    expectation.deliver input = output ↔ Delivers expectation input output :=
  Proofs.Languages.Python.Core.Module.SeededCall.delivers_iff

theorem invoke_iff {callee : Value} {arguments : List Value} {result : Result} :
    invoke callee arguments = result ↔ Executes (Request.decode callee arguments) result :=
  Proofs.Languages.Python.Core.Module.SeededCall.invoke_iff

/-- The stock zero-argument constructor returns the canonical empty tuple
payload carried by the seeded value model. -/
theorem invoke_tuple_empty :
    invoke (.builtin .tuple) [] = .ok (.returnedTuple []) :=
  invoke_iff.mpr .emptyTuple

theorem invoke_int_bool (value : Bool) :
    invoke (.builtin .int) [.bool value] = .ok (.int (Int.ofNat value.toNat)) :=
  invoke_iff.mpr (.intFromBool value)

theorem invoke_stockStr {value : Value} {text : Core.Text} (checked : value.stockStr? = some text) :
    invoke (.builtin .str) [value] = .ok (.text text) := by
  apply invoke_iff.mpr
  simpa [Request.decode, checked] using (Executes.textConversion (arity := 1) text)

theorem invoke_stockBool {value : Value} {result : Bool} (checked : value.stockBool? = some result) :
    invoke (.builtin .bool) [value] = .ok (.bool result) := by
  apply invoke_iff.mpr
  simpa [Request.decode, checked] using (Executes.truthConversion (arity := 1) result)

theorem invoke_assertEqual_text (left right : Core.Text) :
    invoke (.helper .assertEqual) [.text left, .text right] =
      if left = right then .ok .none else .error (.raised (.assertionError (.textPair left right))) := by
  split
  · exact invoke_iff.mpr (.equalText left right ‹_›)
  · exact invoke_iff.mpr (.unequalText left right ‹_›)

theorem invoke_assertIsNot_int_bool (integer : Int) (truth : Bool) :
    invoke (.helper .assertIsNot) [.int integer, .bool truth] = .ok .none :=
  invoke_iff.mpr .distinctIntBool

theorem invoke_callable_len :
    invoke (.builtin .callable) [.builtin .len] = .ok (.bool true) :=
  invoke_iff.mpr (.callable .len)

theorem invoke_callable_int (integer : Int) :
    invoke (.builtin .callable) [.int integer] = .ok (.bool false) :=
  invoke_iff.mpr (.callable .integer)

theorem invoke_isinstance_bool_bool (value : Bool) :
    invoke (.builtin .isinstance) [.bool value, .builtin .bool] = .ok (.bool true) :=
  invoke_iff.mpr (.isinstance .boolAgainstBool)

theorem invoke_isinstance_bool_int (value : Bool) :
    invoke (.builtin .isinstance) [.bool value, .builtin .int] = .ok (.bool true) :=
  invoke_iff.mpr (.isinstance .boolAgainstInt)

theorem invoke_isinstance_int_bool (value : Int) :
    invoke (.builtin .isinstance) [.int value, .builtin .bool] = .ok (.bool false) :=
  invoke_iff.mpr (.isinstance .intAgainstBool)

theorem invoke_assertIs_bool (left right : Bool) :
    invoke (.helper .assertIs) [.bool left, .bool right] =
      if BoolIdentity.ofBool left = BoolIdentity.ofBool right then .ok .none
      else .error (.raised (.assertionError (.booleanPair left right))) := by
  split
  · exact invoke_iff.mpr (.sameBool left right ‹_›)
  · exact invoke_iff.mpr (.distinctBool left right ‹_›)

end Silmaril.Languages.Python.Core.Module.SeededCall
