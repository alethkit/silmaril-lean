module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Straight.Thms

/-! # A typed sum packet selects distinct exits with identical payload types -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Case

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region Transfer)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (iterate_fixpoint)

private abbrev SortName := ULift.{1} Unit
private abbrev Reg := ULift.{1} Nat
private abbrev Label := ULift.{1} Nat
private abbrev Event (_ : Type) := Empty
private abbrev Atom := ULift.{1} Nat

private instance : AtomValues SortName := ⟨fun _ => Atom⟩
private instance : HasTy Empty (Ty SortName) := ⟨Empty.elim, Empty.elim⟩
private instance : HasEff Empty Bool := ⟨Empty.elim⟩

private def signature : FlatInstitution.Signature.{0, 0} SortName where
  Instr := Empty

private instance : DecidableEq signature.Instr := fun f => Empty.elim f

private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))

attribute [local instance] LambdaSSA.Semantics.Interaction.Typed.typeModel

private def model : Model (κ := SortName) Event signature.Instr where
  instructions :=
    { denote := fun f => Empty.elim f
      denotePure := fun f => Empty.elim f
      denote_pure := fun f => Empty.elim f }
  raw := Empty.elim
  compatible := fun f => Empty.elim f

private def num : Ty SortName := .base ⟨()⟩
private def choice : Ty SortName := .coprod num num
private def leftExit : Label := ⟨22⟩
private def rightExit : Label := ⟨11⟩

private abbrev ports : Interface SortName Reg Label :=
  numberedInterface (.snoc .nil choice) [leftExit, rightExit] (fun _ => num)
private def label (_ : Fin 1) : Label := ⟨7⟩
private def fields (_ : Label) : List (Reg × Ty SortName) := [(⟨2⟩, num)]

private def flat : FiniteCFG signature.Instr 1 ports.exits.length ports.slots where
  entry := .br 0 (.bv 0)
  block _ :=
    .case (.bv 0)
      (.br 1 (.pair (.bv 0) (.pair (.bv 0) .unit)))
      (.br 2 (.pair (.bv 0) (.pair (.bv 0) .unit)))

private theorem typed : flat.HasType ports.context (fun _ => choice)
    (LiveOut.exitInterface ports fields).external :=
  NamedFlat.check_sound flat ports.context (fun _ => choice) _ (by decide)

private def lowered : Lowered ports fields flat :=
  (lowerFresh label ports.context ports.exits ports.external fields flat).get (by decide)

-- The actual packet holds the sum argument and one saved sum capture.
example : ∀ i, lowered.savedRegisters i = [⟨0⟩] := by decide

private def profile := (lowered.synthesizeProfile (fun _ => choice)).get (by decide)

example : ∀ i, profile i = .product choice (.product choice .unit) := by decide

private def recompiled : LiveOut.Admission signature ports fields lowered.source :=
  Straight.admitWithCapture lowered (fun _ => choice) (by decide) 0
    (by decide) (by decide) (by decide)

example : (lowered.reAdmit (fun _ => choice)).isSome = true := by decide

private abbrev Input := Ty.denote (AtomValues.carrier (κ := SortName))
  (Region.packedInputType ports.context.toList)

private def input (right : Bool) (n : Nat) : Input :=
  (PUnit.unit, if right then .inr ⟨n⟩ else .inl ⟨n⟩)

private def atom (n : Nat) : Value Runtime := .atom ⟨⟨()⟩, ⟨n⟩⟩
private def value (right : Bool) (n : Nat) : Value Runtime :=
  if right then .inr (atom n) else .inl (atom n)

example (right : Bool) (n : Nat) :
    store ports.version.names ports.context (input right n) (⟨0⟩, 0) = value right n :=
  (Straight.capture_at_version_zero (context := ports.context) 0 (input right n)).trans
    (by cases right <;> rfl)

private def output (right : Bool) (n : Nat) : Transfer Runtime :=
  let packet := (atom n).pair ((atom n).pair .unit)
  (0, if right then .inr (.inl packet) else .inl packet)

example (n : Nat) : output false n ≠ output true n := by
  intro eq
  cases congrArg Prod.snd eq

private def table : List (Label × CFG.Block Reg Label signature.Instr) :=
  [(⟨7⟩, ⟨⟨1⟩, .term (.case (.val (.var ⟨1⟩))
    ⟨2⟩ (.br leftExit (.var ⟨2⟩)) ⟨2⟩ (.br rightExit (.var ⟨2⟩)))⟩)]

private theorem loweredTable : lowered.source.blocks = table := rfl

private def start (right : Bool) (n : Nat) : CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
  (⟨7⟩, value right n, store ports.names ports.context (input right n))

-- The jump carries the actual supplied sum both as its argument and in
-- the saved record. The capture type and value use the same input slot.
example (right : Bool) (n : Nat) :
    CFG.Cyclic.Versioning.encode (treeModel model.raw) (withLiveOut (P := signature) fields lowered.source)
      (start right n) = (⟨7⟩, .pair (value right n) (.pair (value right n) .unit)) := by
  have route : CFG.Cyclic.Versioning.destinations
      (withLiveOut (P := signature) fields lowered.source) (⟨7⟩ : Label) = some [⟨0⟩] := by decide
  have agrees : (start right n).2.2 ⟨0⟩ = inputEnv ports.context (input right n) 0 := by
    cases right <;> rfl
  have packet := Straight.encode_capture lowered model 0 (input right n) (start right n) route agrees
  cases right <;> exact packet

private def done (right : Bool) (n : Nat) : CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
  let σ := upd (start right n).2.2 ⟨1⟩ (value right n)
  (if right then rightExit else leftExit, atom n, upd σ ⟨2⟩ (atom n))

set_option maxRecDepth 2048 in
private theorem named_result (right : Bool) (n : Nat) :
    LiveOut.observe (P := signature) model ports fields lowered.source (input right n) =
      pure (output right n) := by
  let step := CFG.Cyclic.step (treeModel model.raw) lowered.source.blocks
  have selectArm : step (start right n) = pure (.inr (done right n)) := by
    cases right <;>
      simp [step, loweredTable, table, CFG.Cyclic.step, start, done, CFG.Body.exec, CFG.Term.exec,
        Op.eval, Val.eval, treeModel, value, upd]
  have exit : step (done right n) = pure (.inl (done right n)) := by
    cases right <;> rfl
  have enter : CFG.Cyclic.run (treeModel model.raw) lowered.source
      (store ports.names ports.context (input right n)) = iter step (start right n) := by
    cases right <;> rfl
  change (CFG.Cyclic.run (treeModel model.raw) lowered.source
    (store ports.names ports.context (input right n)) >>= _) = _
  rw [enter, congrFun (iterate_fixpoint step) (start right n), selectArm, pure_bind]
  change (iter step (done right n) >>= _) = _
  rw [congrFun (iterate_fixpoint step) (done right n), exit, pure_bind]
  change (pure (done right n) >>= _) = _
  rw [pure_bind]
  cases right <;> rfl

private def packedInput (right : Bool) (n : Nat) : Value Runtime :=
  encodeValue (AtomValues.carrier (κ := SortName))
    (Region.packedInputType ports.context.toList) (input right n)

example (right : Bool) (n : Nat) (ambient : Env Runtime) :
    region model.raw (extend ambient (packedInput right n)) (Program.ofCFGEntry typed).code =
      region model.raw (extend ambient (packedInput right n)) recompiled.program.code :=
  lowered.packed_roundTrip model typed recompiled (input right n) ambient

example (right : Bool) (n : Nat) (ambient : Env Runtime) :
    region model.raw (extend ambient (packedInput right n)) recompiled.program.code =
      pure (output right n) :=
  (recompiled.packed_tree model (input right n) ambient).trans (named_result right n)

/-- Keep the input and the two exits, with the dispatcher in the entry.
The left arm unpacks the same sum again and uses both binder depths. -/
private def entryOnly : FiniteCFG signature.Instr 0 ports.exits.length ports.slots where
  entry := .case (.bv 0)
    (.case (.bv 1)
      (.br 0 (.pair (.bv 0) (.pair (.bv 1) .unit)))
      (.br 0 (.pair (.bv 0) (.pair (.bv 1) .unit))))
    (.br 1 (.pair (.bv 0) (.pair (.bv 0) .unit)))
  block := Fin.elim0

private def entryLowered : Lowered ports fields entryOnly :=
  (lowerFresh Fin.elim0 ports.context ports.exits ports.external fields entryOnly).get (by decide)

private theorem entryTyped : entryOnly.HasType ports.context Fin.elim0
    (LiveOut.exitInterface ports fields).external :=
  NamedFlat.check_sound entryOnly ports.context Fin.elim0 _ (by decide)

-- All obligations concern the original source or the saved-register list.
private def entryAdmission : LiveOut.Admission signature ports fields entryLowered.source :=
  Straight.admit entryLowered Fin.elim0 (by decide) (by decide) (by decide)

private theorem entryShape : entryLowered.source =
    ⟨.term (.case (.val (.var ⟨0⟩)) ⟨2⟩
      (.case (.val (.var ⟨0⟩)) ⟨3⟩ (.br leftExit (.var ⟨3⟩))
        ⟨3⟩ (.br leftExit (.var ⟨3⟩)))
      ⟨2⟩ (.br rightExit (.var ⟨2⟩))), []⟩ := rfl

set_option maxRecDepth 2048 in
private theorem entry_named_result (right : Bool) (n : Nat) :
    LiveOut.observe (P := signature) model ports fields entryLowered.source (input right n) =
      pure (output right n) := by
  let m := treeModel model.raw
  let σ := store ports.names ports.context (input right n)
  let outer := upd σ ⟨2⟩ (atom n)
  let pending : CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
    (if right then rightExit else leftExit, atom n, if right then outer else upd outer ⟨3⟩ (atom n))
  let step := CFG.Cyclic.step m ([] : List (Label × CFG.Block Reg Label signature.Instr))
  have atExit : CFG.Cyclic.run m entryLowered.source σ = iter step pending := by
    have read : σ ⟨0⟩ = value right n := by cases right <;> rfl
    cases right <;> simp [CFG.Cyclic.run, entryShape, CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval,
      step, pending, outer, m, treeModel, value, read, upd]
  have finish : iter step pending = pure pending := by
    rw [congrFun (iterate_fixpoint step) pending]
    change (pure (Sum.inl pending) >>= _) = _
    rw [pure_bind]
    rfl
  change (CFG.Cyclic.run m entryLowered.source σ >>= _) = _
  rw [atExit, finish, pure_bind]
  cases right <;> rfl

example (right : Bool) (n : Nat) (ambient : Env Runtime) :
    region model.raw (extend ambient (packedInput right n)) (Program.ofCFGEntry entryTyped).code =
      region model.raw (extend ambient (packedInput right n)) entryAdmission.program.code :=
  entryLowered.packed_roundTrip model entryTyped entryAdmission (input right n) ambient

-- The entry-only admission agrees with the original internal-block fixture
-- for both ordered exits at every supplied sum.
example (right : Bool) (n : Nat) (ambient : Env Runtime) :
    region model.raw (extend ambient (packedInput right n)) entryAdmission.program.code =
      region model.raw (extend ambient (packedInput right n)) recompiled.program.code :=
  ((entryAdmission.packed_tree model (input right n) ambient).trans
    (entry_named_result right n)).trans
      (((recompiled.packed_tree model (input right n) ambient).trans (named_result right n)).symm)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Case
