module

public import Silmaril.Courses.Cambridge.L3.Exercises.Exceptions

/-! Nested handlers around a recursive CBV call and a store update. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Exercises.Exceptions.Examples

inductive Tag where
  | boom
  | other
  deriving DecidableEq

def cell (n : Int) : Store := (∅ : Store).insert 0 ⟨.int n, .int n⟩

def locations : LocTypes := (∅ : LocTypes).insert 0 .int

def write : Expr Tag := .core (.assign (.loc 0) (.int 7))
def read : Expr Tag := .core (.deref (.loc 0))

/-- On its recursive call the function writes and raises `boom`. The
caller's inner handler catches and re-raises it. Handlers for `other`
forward it to the outermost handler, which reads the current store. -/
def functionBody : Expr Tag :=
  .handle
    (.cond (.var 0)
      (.handle (.app (.var 1) (.core (.bool false))) .boom (.raise .boom))
      (.letE (.core .unit) write (.raise .boom)))
    .other (.core (.int 0))

def program : Expr Tag :=
  .handle (.letRec (.core .bool) (.core .int) functionBody
    (.app (.var 0) (.core (.bool true)))) .boom read

theorem program_typed : HasType locations [] program (.core .int) := by
  have location : locations.lookup 0 = some .int := by simp [locations]
  apply HasType.handle
  · apply HasType.letRec
    · exact .handle
        (.cond (.var rfl)
          (.handle (.app (.var rfl) (.core (.bool false))) (.raise Tag.boom))
          (.letE (.core (.assign (.loc location) (.int 7))) (.raise Tag.boom)))
        (.core (.int 0))
    · exact .app (.var rfl) (.core (.bool true))
  · exact .core (.deref (.loc location))

private abbrev closure : Expr Tag := .recClosure (.core .bool) (.core .int) functionBody

private def invoke (b : Bool) : Expr Tag := .app closure (.core (.bool b))

private theorem write_step : Step ⟨write, cell 0⟩ ⟨.core .skip, cell 7⟩ := by
  have present : 0 ∈ cell 0 := Finmap.mem_insert.mpr (Or.inl rfl)
  have target : (cell 0).insert 0 ⟨.int 7, .int 7⟩ = cell 7 := by
    simp [cell, Finmap.insert_insert]
  rw [← target]
  exact .core (.assignValue ⟨.int 7, .int 7⟩ present)

private theorem recursive_call_raises : Steps ⟨invoke false, cell 0⟩ ⟨.raise .boom, cell 7⟩ := by
  have applyFn : Step ⟨invoke false, cell 0⟩
      ⟨.handle (.cond (.core (.bool false))
        (.handle (invoke false) .boom (.raise .boom))
        (.letE (.core .unit) write (.raise .boom))) .other (.core (.int 0)), cell 0⟩ :=
    .appRec (.core (.bool false))
  have writeSlot : Step ⟨.letE (.core .unit) write (.raise Tag.boom), cell 0⟩
      ⟨.letE (.core .unit) (.core .skip) (.raise .boom), cell 7⟩ :=
    .frame (.letRhs (.core .unit) (.raise Tag.boom)) write_step
  have afterWrite : Step ⟨.letE (.core .unit) (.core .skip) (.raise Tag.boom), cell 7⟩
      ⟨.raise .boom, cell 7⟩ :=
    .letE (.core .skip)
  exact .head applyFn (.head (.handleStep .ifFalse)
    (.head (.handleStep writeSlot) (.head (.handleStep afterWrite) (.single (.miss (by decide))))))

private theorem outer_call_raises : Steps ⟨invoke true, cell 0⟩ ⟨.raise .boom, cell 7⟩ := by
  have applyFn : Step ⟨invoke true, cell 0⟩
      ⟨.handle (.cond (.core (.bool true))
        (.handle (invoke false) .boom (.raise .boom))
        (.letE (.core .unit) write (.raise .boom))) .other (.core (.int 0)), cell 0⟩ :=
    .appRec (.core (.bool true))
  have nested := recursive_call_raises.handle (name := Tag.boom) (recovery := .raise .boom)
  exact .head applyFn
    (.head (.handleStep .ifTrue)
      ((Steps.handle (nested.tail .catchRaise) (name := Tag.other) (recovery := .core (.int 0))).tail
        (.miss (by decide))))

theorem program_returns : Steps ⟨program, cell 0⟩ ⟨.core (.int 7), cell 7⟩ := by
  have enter : Step ⟨program, cell 0⟩ ⟨.handle (invoke true) .boom read, cell 0⟩ :=
    .handleStep .letRec
  have lookup : (cell 7).lookup 0 = some ⟨.int 7, .int 7⟩ := by simp [cell]
  exact .head enter (((outer_call_raises.handle (name := Tag.boom) (recovery := read)).tail
    .catchRaise).tail (.core (.derefValue lookup)))

theorem nearest_handler (s : Store) :
    Steps ⟨.handle (.handle (.raise Tag.boom) .boom (.core (.int 1))) .boom (.core (.int 2)), s⟩
      ⟨.core (.int 1), s⟩ :=
  .head (.handleStep .catchRaise) (.single (.handleValue (.core (.int 1))))

theorem argument_raises (s : Store) :
    Steps ⟨.app (.lam (.core .unit) (.core (.int 1))) (.raise Tag.boom), s⟩
      ⟨.raise .boom, s⟩ :=
  .single (.unwind (.appArg (.lam (.core .unit) (.core (.int 1))) (.lam _ _)) Tag.boom s)

end Silmaril.Courses.Cambridge.L3.Exercises.Exceptions.Examples
