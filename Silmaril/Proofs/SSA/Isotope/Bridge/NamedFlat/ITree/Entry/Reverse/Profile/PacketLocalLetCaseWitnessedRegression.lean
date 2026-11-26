module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.LetCase.Witnessed.Thms

/-! # A written LetCase request and two ordered live-out exits -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed.Tests

open LambdaSSA (Region)
open LambdaSSA.Acyclic (Operand)
open LambdaSSA.Acyclic.Positional.Capture
open LambdaSSA.Acyclic.Positional.Capture.Reverse (ResultGrammar)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues ModelTree)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree (vis diverge vis_bind)
open Isotope.Semantics (encodeValue)
open Isotope.Institution.LetCase.WeakITree (algebra equationRoom)

private abbrev SortName := ULift.{1} Unit
private abbrev Label := ULift.{1} Nat
private abbrev Atom := ULift.{1} Nat

private def num : Ty SortName := .base ⟨()⟩
private def choice : Ty SortName := .coprod num num

private inductive Op : Type 1
  | pick
  deriving DecidableEq

private inductive Event : Type → Type
  | choose : Event Bool

private instance : AtomValues SortName := ⟨fun _ => Atom⟩
private instance : HasTy Op (Ty SortName) := ⟨fun _ => num, fun _ => choice⟩
private instance : HasEff Op Bool := ⟨fun _ => true⟩

private def sig : FlatInstitution.Signature.{0, 1} SortName where
  Instr := Op

private instance : DecidableEq sig.Instr := inferInstanceAs (DecidableEq Op)

private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))
private abbrev C := AtomValues.carrier (κ := SortName)

attribute [local instance] LambdaSSA.Semantics.Interaction.Typed.typeModel

private def model : Model (κ := SortName) Event sig.Instr where
  instructions :=
    { denote := fun _ x => vis Event.choose (fun right => pure (if right then .inr x else .inl x))
      denotePure := fun _ h => nomatch h
      denote_pure := fun _ h => nomatch h }
  raw := fun _ x =>
    match x with
    | .atom n => vis Event.choose (fun right => pure (if right then .inr (.atom n) else .inl (.atom n)))
    | _ => diverge
  compatible := by
    dsimp only
    intro f x
    change (vis Event.choose (fun right => pure (if right then .inr (.atom ⟨⟨()⟩, x⟩)
      else .inl (.atom ⟨⟨()⟩, x⟩)))) =
      (vis Event.choose (fun right => pure (if right then Sum.inr x else Sum.inl x)) >>=
        fun y => pure (encodeValue C choice y))
    rw [vis_bind]
    congr 1
    funext reply
    cases reply <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_bind] <;> rfl

private abbrev context : BoundCtx (Ty SortName) 1 := .snoc .nil num
private abbrev exits : List Label := [⟨22⟩, ⟨11⟩]
private def external (_ : Fin exits.length) : Ty SortName := .unit
private def fields (_ : Label) : List (Register × Ty SortName) := [(⟨1⟩, num)]
private abbrev ports := numberedInterface context exits external
private abbrev D := (LiveOut.exitInterface ports fields).external
private abbrev B := Region.packedExitType (List.ofFn D)
private abbrev A := Region.packedInputType context.toList

-- Written directly in native LetCase syntax. The two tagged packets have
-- the same unit payload but carry the caller's value as a selected live-out.
private def written : Operand sig.Instr context B :=
  ⟨.let₁ (.bv 0) (.case (.op .pick (.bv 0))
      (.let₁ (.pair .unit (.pair (.bv 0) .unit)) (.inl (.bv 0)))
      (.let₁ (.pair .unit (.pair (.bv 0) .unit)) (.inr (.inl (.bv 0))))),
    .let₁ .bv (.case (.op .bv)
      (.let₁ (.pair .unit (.pair .bv .unit)) (.inl .bv))
      (.let₁ (.pair .unit (.pair .bv .unit)) (.inr (.inl .bv))))⟩

private def grammar : ResultGrammar (L := List.ofFn D) written :=
  ⟨⟨num, ⟨.bv 0, .bv⟩, .case ⟨.op .pick (.bv 0), .op .bv⟩
      (.local (.jump ⟨.pair .unit (.pair (.bv 0) .unit), .pair .unit (.pair .bv .unit)⟩ (.exit (i := 0) rfl)))
      (.local (.jump ⟨.pair .unit (.pair (.bv 0) .unit), .pair .unit (.pair .bv .unit)⟩ (.exit (i := 1) rfl)))⟩,
    rfl⟩

private def labels (i : Fin (grammar.toTable.size + 1)) : Label := ⟨7 + i.val⟩

private def compiled : Compiled (fields := fields) grammar :=
  (compile? (fields := fields) grammar labels).get (by decide)

example : grammar.toTable.size + 1 = 3 := rfl

example : (equationRoom sig).Sat (algebra (P := sig) model) compiled.equation :=
  compiled.satisfies model

example : (Program.ofCFGEntry grammar.toTable.toFlat_hasType).denote model =
    compiled.admission.program.denote model :=
  compiled.packed_eq model

private def packet (x : Atom) : Value Runtime := .pair .unit (.pair (.atom ⟨⟨()⟩, x⟩) .unit)

private theorem source_result (x : Atom) :
    (sourceTree (fields := fields) model written (PUnit.unit, x) >>= fun b => pure (0, encodeValue C B b)) =
      vis Event.choose (fun right => pure (0, if right then .inr (.inl (packet x)) else .inl (packet x))) := by
  simp only [sourceTree, written, LetCase.LocallyNameless.Derivation.denote, pure_bind]
  let request (a : Atom) : ModelTree Event (Atom ⊕ Atom) :=
    vis Event.choose (fun right => pure (if right then Sum.inr a else Sum.inl a))
  change ((((pure x : ModelTree Event Atom) >>= request) >>= _) >>= _) = _
  rw [pure_bind]
  change ((vis Event.choose _ >>= _) >>= _) = _
  erw [vis_bind, vis_bind]
  congr 1
  funext right
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> erw [pure_bind] <;>
    dsimp [Semantics.CoproductModel.coprodEquiv, Semantics.ProductModel.productEquiv,
      Semantics.UnitModel.unitEquiv, Semantics.BoundEnv.snoc, Record.field, Equiv.refl, Equiv.symm, DFunLike.coe, EquivLike.coe, Equiv.instEquivLike, id] <;>
    repeat' (first | rfl | erw [pure_bind])

example (x : Atom) :
    LiveOut.observe model ports fields compiled.lowered.source (PUnit.unit, x) =
      vis Event.choose (fun right => pure (0, if right then .inr (.inl (packet x)) else .inl (packet x))) :=
  (compiled.named_tree model (PUnit.unit, x)).symm.trans (source_result x)

example (x : Atom) (ambient : Env Runtime) :
    region model.raw (extend ambient (encodeValue C A (PUnit.unit, x))) compiled.admission.program.code =
      vis Event.choose (fun right => pure (0, if right then .inr (.inl (packet x)) else .inl (packet x))) :=
  (compiled.packed_tree model (PUnit.unit, x) ambient).trans (source_result x)

-- The captured reverse compiler permits this older input read, but the
-- packet-local named emitter has no corresponding block-local name.
private def readsAmbient : Reverse.Program sig.Instr context (List.ofFn D) :=
  ⟨num, ⟨.bv 0, .bv⟩,
    .jump ⟨.pair .unit (.pair (.bv 1) .unit), .pair .unit (.pair .bv .unit)⟩ (.exit (i := 0) rfl)⟩

private def ambientGrammar : ResultGrammar readsAmbient.toLetCase := ⟨readsAmbient, rfl⟩

private def ambientLabels (i : Fin (ambientGrammar.toTable.size + 1)) : Label := ⟨7 + i.val⟩

example : (lower (freshRegisters 1) ports.names ambientLabels (fun i => exits[i])
    (ambientGrammar.toTable.toFlat List.length_ofFn)).isSome = true := by decide

example : (lowerFresh ambientLabels context exits external fields
    (ambientGrammar.toTable.toFlat List.length_ofFn)).isNone = true := by decide

example : (compile? (fields := fields) ambientGrammar ambientLabels).isNone = true := by decide

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed.Tests
