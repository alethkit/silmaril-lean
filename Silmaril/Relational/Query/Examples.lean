module

public import Silmaril.Relational.Query.All

/-! Checked examples using only the public query interface. -/

namespace Silmaril.Relational.QueryExamples

example : ResultRows.support (ResultRows.bagOfList [1, 1]) =
    ResultRows.support (.ordered [1] : ResultRows Nat) := by
  ext row
  simp [ResultRows.support, ResultRows.bagOfList]

example : ResultRows.bagOfList [true, false] = ResultRows.bagOfList [false, true] :=
  congrArg ResultRows.bag (Quot.sound (List.Perm.swap false true []))

example : (ResultRows.ordered [true, false] : ResultRows Bool) ≠ .ordered [false, true] := by
  intro eq
  cases eq

private def readAndIncrement (_ : Unit) : StateM Nat Nat := fun count => (count, count + 1)

example : StatefulQueryRel.ofStateM readAndIncrement 3 () 3 4 := rfl

example : ¬ StatefulQueryRel.ofStateM readAndIncrement 3 () 3 3 := by
  change (3, 4) ≠ ((3, 3) : Nat × Nat)
  decide

example : (StatefulQueryRel.ofStateM readAndIncrement).forgetState 3 () 3 :=
  (StatefulQueryRel.forgetState_iff _ _ _ _).mpr ⟨4, rfl⟩

private def optional (action : Option Nat) : Set Nat := {n | action = some n}

example (eval : Unit → Unit → Option Nat) : QueryRel.ofMonad optional eval = QueryRel.ofPartial eval :=
  rfl

example (eval : Unit → Unit → Option Nat) (next : Nat → Option Nat) :
    QueryRel.ofMonad optional (fun db query => eval db query >>= next) =
      (QueryRel.ofPartial eval).bindResults (fun n => optional (next n)) := by
  apply QueryRel.ofMonad_bind optional optional
  intro action continuation n
  cases action <;> simp [optional]

private def step : Nat → StreamStep Nat Nat String Nat
  | 0 => .yield 7 1
  | 1 => .skip 2
  | _ => .error "cursor closed" 2

example : QueryRel.ofStream (QueryRel.ofTotal fun (_ _ : Unit) => 0)
    (fun (cursor : Nat) action => step cursor = action) () ()
    ⟨[7], .error "cursor closed", 2⟩ :=
  ⟨0, rfl, .yield rfl (.skip rfl (.error rfl))⟩

example : QueryRel.streamPrefixes (QueryRel.ofTotal fun (_ _ : Unit) => ())
    (fun (_ : Unit) (action : StreamStep Unit Nat Unit Unit) => action = .yield 7 ()) () () [7, 7] :=
  ⟨(), rfl, .yield rfl (.yield rfl (.nil ()))⟩

private def choice : QueryRel Unit Unit Bool := fun _ _ _ => True

private def onlyFalse : QueryRel Unit Unit Bool := QueryRel.ofTotal fun _ _ => false

-- A refinement can remain total and still lose completeness.
example : onlyFalse.Total ∧ onlyFalse.Refines choice ∧ ¬ onlyFalse.Complete choice :=
  ⟨QueryRel.ofTotal_total _, fun _ => trivial, fun complete => Bool.noConfusion
    (complete (db := ()) (query := ()) (result := true) trivial)⟩

end Silmaril.Relational.QueryExamples
