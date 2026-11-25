module

public import Silmaril.Courses.Cambridge.Concurrency.Metatheory

/-! # Checked interleavings from pp. 90–91 -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency.Examples

def cell (n : Int) : Store := (∅ : Store).insert "l" n

def write (n : Int) : Expr := .assign "l" (.int n)

def increment (delta : Int) : Expr :=
  .assign "l" (.binary (.int delta) .add (.deref "l"))

def finished (n : Int) : Config := ⟨.parallel .skip .skip, cell n⟩

def writes : Config := ⟨.parallel (write 1) (write 2), cell 0⟩

def race : Config := ⟨.parallel (increment 1) (increment 7), cell 0⟩

def locations : TypeEnv := (∅ : TypeEnv).insert "l" .intref

theorem race_typed : HasType locations race.expr .proc := by
  have present : "l" ∈ locations := by simp [locations]
  exact .parallel
    (.thread (.assign present (.add (.int 1) (.deref present))))
    (.thread (.assign present (.add (.int 7) (.deref present))))

theorem cell_covers (n : Int) : L1.StoreCovers locations (cell n) := by
  intro loc present
  simpa [locations, cell, Finmap.notMem_empty] using present

private theorem write_step (n old : Int) :
    Step ⟨write n, cell old⟩ ⟨.skip, cell n⟩ := by
  have step := Step.assignValue (loc := "l") (s := cell old) (n := n) (by simp [cell])
  simpa only [write, cell, Finmap.insert_insert] using step

private theorem read_increment (delta old : Int) :
    Step ⟨increment delta, cell old⟩
      ⟨.assign "l" (.binary (.int delta) .add (.int old)), cell old⟩ :=
  .assignStep (.binaryRight (.int delta) (.deref (by simp [cell])))

private theorem add_increment (delta read current : Int) :
    Step ⟨.assign "l" (.binary (.int delta) .add (.int read)), cell current⟩
      ⟨write (delta + read), cell current⟩ :=
  .assignStep (.add delta read _)

/-- Whichever atomic write is scheduled last determines the final cell. -/
theorem writes_end_in_one : Steps writes (finished 1) :=
  .head (.parallelRight (write_step 2 0)) (.single (.parallelLeft (write_step 1 2)))

theorem writes_end_in_two : Steps writes (finished 2) :=
  .head (.parallelLeft (write_step 1 0)) (.single (.parallelRight (write_step 2 1)))

private theorem both_read_zero :
    Steps race ⟨.parallel (write 1) (write 7), cell 0⟩ :=
  .head (.parallelLeft (read_increment 1 0))
    (.head (.parallelRight (read_increment 7 0))
      (.head (.parallelLeft (add_increment 1 0 0))
        (.single (.parallelRight (add_increment 7 0 0)))))

/-- Both threads can read zero before either writes. Either update can be lost. -/
theorem race_ends_in_one : Steps race (finished 1) :=
  both_read_zero.trans
    (.head (.parallelRight (write_step 7 0)) (.single (.parallelLeft (write_step 1 7))))

theorem race_ends_in_seven : Steps race (finished 7) :=
  both_read_zero.trans
    (.head (.parallelLeft (write_step 1 0)) (.single (.parallelRight (write_step 7 1))))

/-- The second thread can instead read the result of the first write. -/
theorem race_ends_in_eight : Steps race (finished 8) :=
  .head (.parallelLeft (read_increment 1 0))
    (.head (.parallelLeft (add_increment 1 0 0))
      (.head (.parallelLeft (write_step 1 0))
        (.head (.parallelRight (read_increment 7 1))
          (.head (.parallelRight (add_increment 7 1 1))
            (.single (.parallelRight (write_step 8 1)))))))

theorem finished_lookup (n : Int) : L1.Store.lookup (finished n).store "l" = some n := by
  simp [finished, cell]

theorem finished_terminal (n : Int) : Terminal (finished n) :=
  (ProcessDone.parallel .skip .skip).terminal

-- The original sequencing rule can return a process.
example : HasType ∅ (.seq .skip (.parallel .skip .skip)) .proc :=
  .seq .skip (.parallel (.thread .skip) (.thread .skip))

example : ¬ HasType ∅ (.parallel .skip .skip) .unit := by
  intro typed
  cases typed

end Silmaril.Courses.Cambridge.Concurrency.Examples
