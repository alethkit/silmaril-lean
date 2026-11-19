module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Resources.Thms

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm (AddrType)

variable {E : CoreEngine} {World : Type}

private theorem projectBind {α β γ δ : Type} (eraseIn : α → β) (eraseOut : γ → δ)
    {before : P E World α} {after : P E World β} {left : α → P E World γ}
    {right : β → P E World δ} (first : eraseIn <$> before = after)
    (next : ∀ input, eraseOut <$> left input = right (eraseIn input)) :
    eraseOut <$> (before >>= left) = after >>= right := by
  rw [map_bind, ← first, bind_map_left]
  exact congrArg (fun cont => before >>= cont) (funext next)

private theorem fixedBind {α β γ : Type} (erase : β → γ) {step : P E World α}
    {left : α → P E World β} {right : α → P E World γ}
    (next : ∀ input, erase <$> left input = right input) :
    erase <$> (step >>= left) = step >>= right := by
  rw [map_bind]
  exact congrArg (fun cont => step >>= cont) (funext next)

private theorem projectList {α : Type} {left : α → P E World Observed}
    {right : α → P E World Val} (agree : ∀ input, Observed.value <$> left input = right input)
    (inputs : List α) :
    List.map Observed.value <$> Prog.mapM left inputs = Prog.mapM right inputs := by
  induction inputs with
  | nil => simp only [Prog.mapM_nil, ← Prog.pure_eq, map_pure, List.map_nil]
  | cons head tail ih =>
    simp only [Prog.mapM_cons]
    exact projectBind Observed.value (List.map Observed.value) (agree head) fun _ =>
      projectBind (List.map Observed.value) (List.map Observed.value) ih fun _ => rfl

private theorem projectRange (limits : Limits) (cx : LiftLowerContext E) (layout : Layout)
    {left : Nat → P E World Observed} {right : Nat → P E World Val}
    (agree : ∀ ptr, Observed.value <$> left ptr = right ptr) (ptr len : Nat) :
    List.map Observed.value <$> loadListFromRangeWith limits cx layout left ptr len =
      loadListFromRangeWith limits cx layout right ptr len := by
  unfold loadListFromRangeWith loadListFromValidRangeWith
  exact fixedBind _ fun _ => fixedBind _ fun _ => fixedBind _ fun _ => projectList (fun _ => agree _) _

private theorem projectItems (limits : Limits) (cx : LiftLowerContext E) (width : AddrType)
    (layout : Layout) {left : Nat → P E World Observed} {right : Nat → P E World Val}
    (agree : ∀ ptr, Observed.value <$> left ptr = right ptr) (ptr : Nat) :
    List.map Observed.value <$> loadListWith limits cx width layout left ptr =
      loadListWith limits cx width layout right ptr := by
  unfold loadListWith
  exact fixedBind _ fun base => fixedBind _ fun len => projectRange limits cx layout agree base len

private theorem projectVariant (cx : LiftLowerContext E) (count : Nat) (alignment : Alignment)
    {left : Nat → Nat → P E World (Option Observed)} {right : Nat → Nat → P E World (Option Val)}
    (agree : ∀ index ptr, Option.map Observed.value <$> left index ptr = right index ptr) (ptr : Nat) :
    Observed.value <$> loadVariantUsing cx count alignment Observed.variant left ptr =
      loadVariantWith cx count alignment right ptr := by
  unfold loadVariantUsing loadVariantWith
  exact fixedBind _ fun discr => fixedBind _ fun _ =>
    projectBind (Option.map Observed.value) Observed.value (agree discr.toNat _) fun _ => rfl

private theorem ordinary_value (action : P E World Val) :
    Observed.value <$> (Observed.ordinary <$> action) = action := by
  rw [Functor.map_map]
  exact id_map action

private theorem own_value (cx : LiftLowerContext E) (resource : RtId) (slot : Nat) :
    Observed.value <$> (Resources.takeWith cx resource slot (Observed.own resource) :
      P E World Observed) = (do return .own (← liftOwn Limits.spec cx resource slot)) := by
  change (Resources.takeWith cx resource slot (Observed.own resource)).bind
    (fun value => Prog.pure value.value) = _
  simp only [Resources.takeWith, liftOwn, Observed.own, Prog.bind_eq,
    Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']

variable (limits : Limits) (quirks : Quirks) (cx : LiftLowerContext E) (width : AddrType)

local notation "ownerCarrier" => carrier (World := World) limits quirks cx
local notation "readOwned" => loadAtWith limits cx width ownerCarrier
local notation "readVal" => loadAt (σ := World) limits quirks cx width

mutual
  theorem project : ∀ (type : WIT.ClosedType RtId) (ptr : Nat),
      Observed.value <$> readOwned type ptr = readVal type ptr
    | .prim prim, ptr => by
      simp only [loadAt, loadAtWith]; exact ordinary_value _
    | .ref impossible, _ => nomatch impossible
    | .list item, ptr => by
      simp only [loadAt, loadAtWith]
      exact projectBind (List.map Observed.value) Observed.value
        (projectItems limits cx width _ (project item) ptr) (fun _ => rfl)
    | .fixedList item count, ptr => by
      simp only [loadAt, loadAtWith, loadListFromValidRangeWith]
      exact projectBind (List.map Observed.value) Observed.value
        (projectList (fun _ => project item _) (List.range count))
        (fun _ => rfl)
    | .record fields, ptr => by
      simp only [loadAt, loadAtWith]
      exact projectBind (List.map Observed.value) Observed.value (projectFields fields ptr)
        (fun _ => rfl)
    | .tuple types, ptr => by
      simp only [loadAt, loadAtWith]
      exact projectBind (List.map Observed.value) Observed.value (projectTypes types ptr)
        (fun _ => rfl)
    | .variant cases, ptr => by
      simp only [loadAt, loadAtWith]
      exact projectVariant cx _ _ (projectCases cases) ptr
    | .enum labels, ptr => by
      simp only [loadAt, loadAtWith]
      exact projectVariant cx _ _ (fun _ _ => rfl) ptr
    | .flags labels, ptr => by
      simp only [loadAt, loadAtWith]; exact ordinary_value _
    | .option item, ptr => by
      simp only [loadAt, loadAtWith]
      apply projectVariant
      intro index addr
      cases index with
      | zero => rfl
      | succ index =>
        cases index with
        | zero =>
          exact projectBind Observed.value (Option.map Observed.value) (project item addr) (fun _ => rfl)
        | succ _ => rfl
    | .result ok err, ptr => by
      simp only [loadAt, loadAtWith]
      apply projectVariant
      intro index addr
      cases index with
      | zero => exact projectOptional ok addr
      | succ index =>
        cases index with
        | zero => exact projectOptional err addr
        | succ _ => rfl
    | .map key item, ptr => by
      simp only [loadAt, loadAtWith]
      refine projectBind (List.map Observed.value) Observed.value
        (projectItems limits cx width _ ?_ ptr) (fun _ => rfl)
      intro addr
      unfold loadMapEntryUsing
      refine projectBind Observed.value Observed.value (ordinary_value _) fun _ =>
        projectBind Observed.value Observed.value (project item _) fun _ => ?_
      rfl
    | .own resource, ptr => by
      simp only [loadAt, loadAtWith]
      exact fixedBind _ fun bits => own_value cx resource bits.toNat
    | .borrow resource, ptr => by
      simp only [loadAt, loadAtWith]; exact ordinary_value _
    | .stream item, ptr => by
      simp only [loadAt, loadAtWith]; exact ordinary_value _
    | .future item, ptr => by
      simp only [loadAt, loadAtWith]; exact ordinary_value _
    | .errorContext, ptr => by
      simp only [loadAt, loadAtWith]; exact ordinary_value _
  termination_by structural type => type

  theorem projectFields : ∀ (fields : List (String × WIT.ClosedType RtId)) (ptr : Nat),
      List.map Observed.value <$> loadFieldsAtWith limits cx width ownerCarrier fields ptr =
        loadFieldsAt limits quirks cx width fields ptr
    | [], _ => by simp only [loadFieldsAt, loadFieldsAtWith]; rfl
    | (_, item) :: fields, ptr => by
      simp only [loadFieldsAt, loadFieldsAtWith]
      exact projectBind Observed.value (List.map Observed.value) (project item _) fun _ =>
        projectBind (List.map Observed.value) (List.map Observed.value)
          (projectFields fields _) (fun _ => rfl)
  termination_by structural fields => fields

  theorem projectTypes : ∀ (types : List (WIT.ClosedType RtId)) (ptr : Nat),
      List.map Observed.value <$> loadTypesAtWith limits cx width ownerCarrier types ptr =
        loadTypesAt limits quirks cx width types ptr
    | [], _ => by simp only [loadTypesAt, loadTypesAtWith]; rfl
    | item :: types, ptr => by
      simp only [loadTypesAt, loadTypesAtWith]
      exact projectBind Observed.value (List.map Observed.value) (project item _) fun _ =>
        projectBind (List.map Observed.value) (List.map Observed.value)
          (projectTypes types _) (fun _ => rfl)
  termination_by structural types => types

  theorem projectCases : ∀ (cases : List (String × Option (WIT.ClosedType RtId))) (index ptr : Nat),
      Option.map Observed.value <$> loadCaseAtWith limits cx width ownerCarrier cases index ptr =
        loadCaseAt limits quirks cx width cases index ptr
    | [], _, _ => by simp only [loadCaseAt, loadCaseAtWith]; rfl
    | (_, item) :: _, 0, ptr => by
      simp only [loadCaseAt, loadCaseAtWith]; exact projectOptional item ptr
    | _ :: cases, index + 1, ptr => by
      simp only [loadCaseAt, loadCaseAtWith]; exact projectCases cases index ptr
  termination_by structural cases => cases

  theorem projectOptional : ∀ (item : Option (WIT.ClosedType RtId)) (ptr : Nat),
      Option.map Observed.value <$> loadOptAtWith limits cx width ownerCarrier item ptr =
        loadOptAt limits quirks cx width item ptr
    | none, _ => by simp only [loadOptAt, loadOptAtWith]; rfl
    | some item, ptr => by
      simp only [loadOptAt, loadOptAtWith]
      exact projectBind Observed.value (Option.map Observed.value) (project item ptr) (fun _ => rfl)
  termination_by structural item => item
end

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory
