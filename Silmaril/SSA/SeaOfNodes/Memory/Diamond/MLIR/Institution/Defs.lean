module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Defs

/-! Equation observations of the actual two-cell MLIR CF lowering. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution renaming
  Signature → EntrySignature, Model → NativeModel, Equation → NativeEquation
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF (Cfg)
open RVSDG (Tuple)

variable {P Q : EntrySignature} {args : List ValueSort}

/-- An assignment to the source entry ports at exactly two initialized cells. -/
abbrev Valuation (P : EntrySignature) := Tuple (Val 2) P.args

def nativeModel (input : Valuation P) : NativeModel P := ⟨2, input⟩

/-- Use the native model reduct at the fixed cell count. -/
def pullback (h : P ⟶ Q) (input : Valuation Q) : Valuation P :=
  (Diamond.Institution.reduct h (nativeModel input)).input

/-- Keep the actual emitted CFG and a proof that it is in the lowering's image. -/
abbrev Program (args : List ValueSort) :=
  {cfg : Cfg Op Label (entryTypes args) resultTypes // ∃ graph : Graph args, lower graph = cfg}

def emit (graph : Graph args) : Program args := ⟨lower graph, ⟨graph, rfl⟩⟩

/-- Entry, the selected arm and the shared suffix each consume one block tick.
The result contains the word and both cells. -/
def Program.observe (program : Program args) (input : Tuple (Val 2) args)
    (guard : Bool) (initial : Heap 2) : Option (Env resultTypes) :=
  program.val.run evalOp 3 (encodeEntry guard input initial)

structure CompiledEquation (P : EntrySignature) where
  lhs : Program P.args
  rhs : Program P.args

def translateEquation (e : NativeEquation P) : CompiledEquation P :=
  ⟨emit e.lhs, emit e.rhs⟩

def CompiledEquation.Holds (e : CompiledEquation P) (input : Valuation P) : Prop :=
  ∀ guard initial, e.lhs.observe input guard initial = e.rhs.observe input guard initial

/-- The room at a typed entry boundary, with the two-cell valuations. -/
def room (P : EntrySignature) : Room.{0, 0, 0} where
  Sen := CompiledEquation P
  Mod := Cat.of (Discrete (Valuation P))
  Sat m e := e.Holds m.as

/-- Native validity restricted to assignments at cell count two. -/
def HoldsTwoCells (e : NativeEquation P) : Prop :=
  ∀ input : Valuation P, (Diamond.Institution.room P).Sat (Discrete.mk (nativeModel input)) e

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution
