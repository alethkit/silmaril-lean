module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.Thms

/-! # A write-only register becomes observable through the generated packet -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.Examples

open Silmaril.SSA.LambdaRTL
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region Transfer)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree HasTrace Trace TraceLE iterate_fixpoint out_ret)

private abbrev SortName := ULift.{1} Unit
private abbrev Reg := ULift.{1} (Fin 4)
private abbrev Label := ULift.{1} (Fin 2)
private abbrev Event (_ : Type) := Empty
private abbrev Atom := ULift.{1} Nat

private instance : AtomValues SortName := ⟨fun _ => Atom⟩
private instance : HasTy Empty (Ty SortName) := ⟨Empty.elim, Empty.elim⟩
private instance : HasEff Empty Bool := ⟨Empty.elim⟩

private def signature : FlatInstitution.Signature.{0, 0} SortName where
  Instr := Empty

private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))

attribute [local instance] LambdaSSA.Semantics.Interaction.Typed.typeModel

private def model : Model (κ := SortName) Event signature.Instr where
  instructions :=
    { denote := fun f => Empty.elim f
      denotePure := fun f => Empty.elim f
      denote_pure := fun f => Empty.elim f }
  raw := Empty.elim
  compatible := fun f => Empty.elim f

private def left : Reg := ⟨0⟩
private def right : Reg := ⟨1⟩
private def saved : Reg := ⟨2⟩
private def param : Reg := ⟨3⟩
private def blockLabel : Label := ⟨0⟩
private def exitLabel : Label := ⟨1⟩
private def num : Ty SortName := .base ⟨()⟩

private def names (i : Fin 2) : Reg := if i = 0 then right else left

private def ports : Interface SortName Reg Label :=
  ⟨2, .snoc (.snoc .nil num) num, names,
    (show ∀ i j : Fin 2, names i = names j → i = j from by decide),
    [exitLabel], fun _ => .unit⟩

private def fields (_ : Label) : List (Reg × Ty SortName) := [(saved, num)]

private def source (read : Reg) : CFG Reg Label signature.Instr :=
  ⟨.let1 saved (.val (.var read)) (.term (.br blockLabel .unit)),
    [(blockLabel, ⟨param, .term (.br exitLabel .unit)⟩)]⟩

-- The added exit read is across an internal transfer. It requires the
-- versioned edge packet to carry a register the old syntax only writes.
example : (CFG.Cyclic.Versioning.registers (source left)).contains saved = false := by decide

example : (CFG.Cyclic.Versioning.registers
    (CFG.Cyclic.LiveOut.attach (fun _ => [saved]) (source left))).contains saved = true := by decide

private def edgeType : Ty SortName := .product .unit (.product num (.product num .unit))

private def leftProgram : Admission signature ports fields (source left) :=
  (admit (P := signature) ports fields (source left) (fun _ => edgeType)).get (by decide)

private def rightProgram : Admission signature ports fields (source right) :=
  (admit (P := signature) ports fields (source right) (fun _ => edgeType)).get (by decide)

-- The same executable checker rejects an incorrect declared field type.
example : (admit (P := signature) ports (fun _ => [(saved, Ty.unit)])
    (source left) (fun _ => edgeType)).isNone = true := by decide

private abbrev Input := Ty.denote (AtomValues.carrier (κ := SortName))
  (LambdaSSA.Region.packedInputType ports.context.toList)

private def sample : Input := ((PUnit.unit, ⟨7⟩), ⟨9⟩)
private def atom (n : Nat) : Value Runtime := .atom ⟨⟨()⟩, ⟨n⟩⟩
private def ambient : Env Runtime := fun _ => .unit

private def inputStore (x : Input) : Reg → Value Runtime := store ports.names ports.context x

private def afterWrite (read : Reg) (x : Input) : Reg → Value Runtime :=
  upd (inputStore x) saved (inputStore x read)

private theorem run_source (read : Reg) (x : Input) :
    CFG.Cyclic.run (treeModel model.raw) (source read) (inputStore x) =
      pure (exitLabel, .unit, upd (afterWrite read x) param .unit) := by
  let step := CFG.Cyclic.step (treeModel model.raw) (source read).blocks
  let start : CFG.Cyclic.Transfer Reg Label (Value Runtime) := (blockLabel, .unit, afterWrite read x)
  let finish : CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
    (exitLabel, .unit, upd (afterWrite read x) param .unit)
  change (pure (inputStore x read) >>= fun v =>
    iter step (blockLabel, .unit, upd (inputStore x) saved v)) = _
  rw [pure_bind]
  change iter step start = pure finish
  rw [congrFun (iterate_fixpoint step) start]
  rw [show step start = pure (.inr finish) from rfl, pure_bind]
  change iter step finish = pure finish
  rw [congrFun (iterate_fixpoint step) finish]
  rw [show step finish = pure (.inl finish) from rfl, pure_bind]
  rfl

-- The existing forgetful observation has the same exit and old payload for
-- every supplied record, even though the two assignments differ.
example (x : Input) :
    obs <$> CFG.Cyclic.run (treeModel model.raw) (source left) (inputStore x) =
      obs <$> CFG.Cyclic.run (treeModel model.raw) (source right) (inputStore x) := by
  simp only [run_source, map_pure, obs]

private def result (n : Nat) : Transfer Runtime :=
  (0, .inl (.pair .unit (.pair (atom n) .unit)))

private theorem left_observation : observe (P := signature) model ports fields (source left) sample =
    pure (result 7) := by
  change (CFG.Cyclic.run (treeModel model.raw) (source left) (inputStore sample) >>= _) = _
  rw [run_source, pure_bind]
  rfl

private theorem right_observation : observe (P := signature) model ports fields (source right) sample =
    pure (result 9) := by
  change (CFG.Cyclic.run (treeModel model.raw) (source right) (inputStore sample) >>= _) = _
  rw [run_source, pure_bind]
  rfl

private def encodedSample : Value Runtime :=
  encodeValue (AtomValues.carrier (κ := SortName)) (LambdaSSA.Region.packedInputType ports.context.toList) sample

example : region model.raw (extend ambient encodedSample) leftProgram.program.code = pure (result 7) :=
  (leftProgram.packed_tree model sample ambient).trans left_observation

example : region model.raw (extend ambient encodedSample) rightProgram.program.code = pure (result 9) :=
  (rightProgram.packed_tree model sample ambient).trans right_observation

example : ¬ model.Satisfies leftProgram.program rightProgram.program := by
  intro sat
  have h := ((satisfies_iff model leftProgram rightProgram ambient).mp sat) sample
  have distinct : ¬ TraceLE (pure (result 7) : Tree Event (Transfer Runtime)) (pure (result 9)) := by
    intro order
    have bad := order (.result (result 7)) (out_ret _)
    have tagged := (out_ret (E := Event) (result 9)).symm.trans bad
    have eq := Silmaril.Elgot.ITree.Visible.ret.inj (Part.some_inj.mp tagged)
    simp [result, atom] at eq
    exact (by decide : (9 : Nat) ≠ 7) (congrArg ULift.down eq)
  rw [left_observation, right_observation] at h
  exact distinct h

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.Examples
