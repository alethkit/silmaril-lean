module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family

open Silmaril.SSA.SeaOfNodes
open Diamond (ValueSort)
open GVN.Cyclic.TwoBackedges (Invariant Keys WordSlot numbering)
open GVN.Cyclic.TwoBackedges.Family
open GVN.WordNumber (Key)
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Program)

variable {regs : List (ValueSort Unit)}

private theorem merge_get (keys : Keys regs) (eq : Equation regs) (port : WordSlot regs) :
    (mergeKeys keys eq).get port =
      if (keys.get port).matches (keys.get eq.member) then keys.get eq.representative else keys.get port :=
  Quads.get_tabulate _ port

private theorem merge_equates (keys : Keys regs) (eq : Equation regs) :
    (mergeKeys keys eq).get eq.representative = (mergeKeys keys eq).get eq.member := by
  have self : (keys.get eq.member).matches (keys.get eq.member) = true := Key.matches_self _
  rw [merge_get, merge_get, self]
  split <;> rfl

private theorem fold_keeps (equations : Equations regs) (keys : Keys regs)
    (first second : WordSlot regs) (same : keys.get first = keys.get second) :
    (equations.foldl mergeKeys keys).get first = (equations.foldl mergeKeys keys).get second := by
  induction equations generalizing keys with
  | nil => exact same
  | cons eq rest ih =>
    apply ih
    rw [merge_get, merge_get, same]

private theorem fold_equates (equations : Equations regs) (keys : Keys regs)
    (eq : Equation regs) (mem : eq ∈ equations) :
    (equations.foldl mergeKeys keys).get eq.representative = (equations.foldl mergeKeys keys).get eq.member := by
  induction equations generalizing keys with
  | nil => cases mem
  | cons head tail ih =>
    rcases List.mem_cons.mp mem with rfl | later
    · exact fold_keeps tail (mergeKeys keys eq) _ _ (merge_equates keys eq)
    · exact ih (mergeKeys keys head) later

theorem seed_matches (equations : Equations regs) : matchesAll equations (seed equations) = true := by
  apply List.all_eq_true.mpr
  intro eq mem
  rw [show (seed equations).get eq.representative = (seed equations).get eq.member from
    fold_equates equations _ eq mem]
  exact Key.matches_self _

private theorem merge_reads {keys : Keys regs} {old : Bank (regs := regs) model} (eq : Equation regs)
    (reads : Keys.Reads old keys old) (same : old.get eq.representative = old.get eq.member) :
    Keys.Reads old (mergeKeys keys eq) old := by
  intro port
  rw [merge_get]
  split
  · rename_i matched
    have equal := Keys.reads_match reads (first := port) (second := eq.member) matched
    exact (reads eq.representative).trans (same.trans equal.symm)
  · exact reads port

private theorem fold_reads (equations : Equations regs) (keys : Keys regs) (old : Bank (regs := regs) model)
    (reads : Keys.Reads old keys old) (assumes : Holds equations old) :
    Keys.Reads old (equations.foldl mergeKeys keys) old := by
  induction equations generalizing keys with
  | nil => exact reads
  | cons eq tail ih =>
    exact ih (mergeKeys keys eq) (merge_reads eq reads (assumes eq (List.mem_cons_self ..)))
      (fun next mem => assumes next (List.mem_cons_of_mem eq mem))

private theorem seed_reads (equations : Equations regs) (old : Bank (regs := regs) model)
    (assumes : Holds equations old) : Keys.Reads old (seed equations) old :=
  fold_reads equations _ old (Keys.reads_entry old) assumes

private theorem holds_of_matches {equations : Equations regs} {keys : Keys regs}
    {anchor values : Bank (regs := regs) model} (reads : Keys.Reads anchor keys values)
    (matched : matchesAll equations keys = true) : Holds equations values :=
  fun eq mem => Keys.reads_match reads (List.all_eq_true.mp matched eq mem)

variable {p : Program Opcode regs word} {equations : Equations regs} {replacement : WordSlot regs}

theorem certificate_invariant (cert : Certificate p equations replacement) : Invariant p (Holds equations) where
  entry input := holds_of_matches (Keys.reads_block p.preheader input (Keys.reads_entry input)) cert.entry
  feedback side old assumes :=
    holds_of_matches
      (Keys.reads_block (p.feedback side) old (Keys.reads_block p.header old (seed_reads equations old assumes)))
      (cert.feedback side)

theorem certificate_observes (cert : Certificate p equations replacement)
    (old : Bank (regs := regs) model) (assumes : Holds equations old) :
    (p.header.eval model old).get p.result = (p.header.eval model old).get replacement :=
  Keys.reads_match (Keys.reads_block p.header old (seed_reads equations old assumes)) cert.exit

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family
