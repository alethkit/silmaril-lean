module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf.Scratch
public import Silmaril.Languages.Starlark.Lists.Iteration.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Comprehensions
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf

local notation "saved" => patternSlot 0 0
local notation "firstSlot" => patternSlot 1 0
local notation "secondSlot" => patternSlot 1 1

private theorem nat_zero_string : toString (0 : Nat) = "0" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide), Nat.digitChar_eq_zero.mpr rfl]
  decide

private theorem nat_one_string : toString (1 : Nat) = "1" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide), Nat.digitChar_eq_one.mpr rfl]
  decide

private theorem nat_two_string : toString (2 : Nat) = "2" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by decide), Nat.digitChar_eq_two.mpr rfl]
  decide

@[local simp] private theorem arg01 : (argumentSlot 0 == argumentSlot 1) = false := by
  simp only [argumentSlot, nat_zero_string, nat_one_string]
  decide

@[local simp] private theorem arg02 : (argumentSlot 0 == argumentSlot 2) = false := by
  simp only [argumentSlot, nat_zero_string, nat_two_string]
  decide

@[local simp] private theorem arg12 : (argumentSlot 1 == argumentSlot 2) = false := by
  simp only [argumentSlot, nat_one_string, nat_two_string]
  decide

@[local simp] private theorem saveFirst : (saved == firstSlot) = false := by
  simp only [patternSlot, nat_zero_string, nat_one_string]
  decide

@[local simp] private theorem saveSecond : (saved == secondSlot) = false := by
  simp only [patternSlot, nat_zero_string, nat_one_string]
  decide

@[local simp] private theorem firstSecond : (firstSlot == secondSlot) = false := by
  simp only [patternSlot, nat_zero_string, nat_one_string]
  decide

private theorem read_exec (program : Program) (available : List DeclarationId) (state : State) (source : Binding) :
    ExecExpr program available state (readOperand source) (state.read (.bound source)) :=
  .evaluates (calls := fun _ _ _ => False) (fun _ _ _ impossible => impossible.elim) (.atom trivial .read)

private theorem assign_read (program : Program) (available : List DeclarationId) (state : State)
    (destination source : Binding) :
    denoteBody program available (.assignExpr destination (readOperand source)) state =
      (state.read (.bound source)).resume (fun value next => .ok .next (next.write destination value)) :=
  (exec_iff_denoteBody _ _ _ _ _).mp (.assignExpr (read_exec program available state source))

private theorem return_read (program : Program) (available : List DeclarationId) (state : State) (source : Binding) :
    denoteBody program available (.returnExpr (readOperand source)) state =
      (state.read (.bound source)).resume (fun value => pure (.returned value)) :=
  (exec_iff_denoteBody _ _ _ _ _).mp (.returnExpr (read_exec program available state source))

private theorem unpack_read (program : Program) (available : List DeclarationId) (state : State)
    (destination : List Binding) (source : Binding) (value : Value)
    (read : state.bindingValue source = .ok value) :
    denoteBody program available (.assignTargetExpr (.unpack destination) (readOperand source)) state =
      Outcome.resume (bindTarget (.unpack destination) value state) fun () => pure .next := by
  have read := read_exec program available state source
  rw [show state.read (.bound source) = .ok value state by simp [State.read, ‹_ = _›]] at read
  exact (exec_iff_denoteBody _ _ _ _ _).mp (.assignTargetExpr read
    ((bindsTarget_iff_bindTarget _ _ _ _).mpr rfl))

private theorem raw_store (program : Program) (available : List DeclarationId) (state : State)
    (receiver index rhs : Binding) (collection offset value : Value)
    (recv : state.bindingValue receiver = .ok collection) (sub : state.bindingValue index = .ok offset)
    (right : state.bindingValue rhs = .ok value) :
    denoteBody program available (.setIndexExpr (readOperand receiver) (readOperand index) (readOperand rhs)) state =
      Outcome.resume (writeIndex collection offset value state) fun () => pure .next := by
  have resolved (binding : Binding) (value : Value) (read : state.bindingValue binding = .ok value) :
      ExecExpr program available state (readOperand binding) (.ok value state) := by
    simpa [State.read, read] using read_exec program available state binding
  exact (exec_iff_denoteBody _ _ _ _ _).mp (.setIndexExpr (resolved _ _ right) (resolved _ _ recv) (resolved _ _ sub))

private theorem frame_eq (edits : Edits) (start finish : State)
    (slots : finish.slots = start.slots) (bindings : finish.bindings = start.bindings) :
    withFrame finish (patch edits start) = patch edits finish := by
  simp [withFrame, patch, slots, bindings]

private theorem stored_frame (state stateWithTemp : State) (edits : Edits)
    (collection offset value : Value) :
    completeCall (patch edits state) none
      (Outcome.resume (writeIndex collection offset value (withFrame state stateWithTemp))
        fun () => pure .next) =
      mapState (patch edits) (Outcome.resume (writeIndex collection offset value state) fun () => pure .next) := by
  rw [write_with_frame]
  cases h : writeIndex collection offset value state with
  | error err final =>
    obtain ⟨slots, bindings⟩ := write_frame (successValue := ()) (.inr h)
    change EStateM.Result.error _ (withFrame final (patch edits state)) = .error _ (patch edits final)
    rw [frame_eq edits state final slots bindings]
  | ok result final =>
    obtain ⟨slots, bindings⟩ := write_frame (error := .indexTarget) (.inl h)
    cases result
    change EStateM.Result.ok Flow.next (withFrame final (patch edits state)) = .ok .next (patch edits final)
    rw [frame_eq edits state final slots bindings]

private theorem private_outside (edits : Edits) (key : Binding) (legal : key.name.toList.head? ≠ some '$')
    (privateKeys : ∀ other ∈ keys edits, other.name.toList.head? = some '$') : key ∉ keys edits :=
  fun present => legal (privateKeys key present)

private theorem edit_private (key : Binding) (value : Option Value) (edits : Edits)
    (privateKey : key.name.toList.head? = some '$')
    (rest : ∀ other ∈ keys edits, other.name.toList.head? = some '$') :
    ∀ other ∈ keys ((key, value) :: edits), other.name.toList.head? = some '$' := by
  intro other present
  rcases List.mem_cons.mp present with rfl | member
  · exact privateKey
  · exact rest other member

/-- The scope around the store drops its argument staging, keeping the
already completed name write in the underlying frame. -/
private theorem staged_store (program : Program) (available : List DeclarationId) (plan : Plan)
    (legal : plan.Legal) (state : State) (edits : Edits) (clean : noPrivateSlots state)
    (privateKeys : ∀ other ∈ keys edits, other.name.toList.head? = some '$')
    (value : Value) (savedValue : edits.lookup secondSlot = some (some value)) :
    denoteBody program available
      (setIndexCode (.plain (readOperand plan.receiver)) (.plain (readOperand plan.index))
        (.plain (readOperand secondSlot)) directStages) (patch edits state) =
      mapState (patch edits) ((store plan value state).resume fun () => pure .next) := by
  let a := argumentSlot 0
  let b := argumentSlot 1
  let c := argumentSlot 2
  let edit₁ : Edits := (a, some value) :: edits
  have seen := patch_read_found edits secondSlot value state (clean _ (private_pattern _ _)) savedValue
  have arg0 := private_write edits state (argumentSlot 0) value (clean _ (private_argument _))
  rw [setIndexCode, denoteBody]
  simp only [Expression.compile, directStages, readSaved]
  rw [denoteBody, assign_read]
  simp only [State.read, seen, Outcome.resume, arg0]
  change completeCall (patch edits state) none
    (denoteBody program available
      (.seq (.assignExpr b (readOperand plan.receiver))
        (.seq (.assignExpr c (readOperand plan.index))
          (.setIndexExpr (readOperand b) (readOperand c) (readOperand a)))) (patch edit₁ state)) = _
  have recv := patch_read edit₁ plan.receiver
    (private_outside edit₁ _ (legal _ (by simp)) (edit_private _ _ _ (private_argument _) privateKeys)) state
  rw [denoteBody, assign_read]
  simp only [State.read, recv]
  cases receiver : state.bindingValue plan.receiver with
  | error error => simp [store, State.read, receiver, Outcome.resume, mapState, completeCall, restoreCaller, patch, edit₁]
  | ok collection =>
    let edit₂ : Edits := (b, some collection) :: edit₁
    have arg1 := private_write edit₁ state b collection (clean _ (private_argument _))
    simp only [Outcome.resume, arg1]
    change completeCall (patch edits state) none
      (denoteBody program available
        (.seq (.assignExpr c (readOperand plan.index))
          (.setIndexExpr (readOperand b) (readOperand c) (readOperand a))) (patch edit₂ state)) = _
    have sub := patch_read edit₂ plan.index
      (private_outside edit₂ _ (legal _ (by simp))
        (edit_private _ _ _ (private_argument _) (edit_private _ _ _ (private_argument _) privateKeys))) state
    rw [denoteBody, assign_read]
    simp only [State.read, sub]
    cases index : state.bindingValue plan.index with
    | error error => simp [store, State.read, receiver, index, Outcome.resume, mapState, completeCall,
        restoreCaller, patch, edit₂, edit₁]
    | ok offset =>
      let edit₃ : Edits := (c, some offset) :: edit₂
      have arg2 := private_write edit₂ state c offset (clean _ (private_argument _))
      simp only [Outcome.resume, arg2]
      change completeCall (patch edits state) none
        (denoteBody program available (.setIndexExpr (readOperand b) (readOperand c) (readOperand a))
          (patch edit₃ state)) = _
      rw [raw_store _ _ _ _ _ _ collection offset value
        (patch_read_found edit₃ b collection state (clean _ (private_argument _)) (by simp [a, b, c, edit₃, edit₂, edit₁, List.lookup_cons]))
        (patch_read_found edit₃ c offset state (clean _ (private_argument _)) (by simp [a, b, c, edit₃, edit₂, edit₁]))
        (patch_read_found edit₃ a value state (clean _ (private_argument _)) (by simp [a, b, c, edit₃, edit₂, edit₁, List.lookup_cons]))]
      change completeCall (patch edits state) none
        (Outcome.resume (writeIndex collection offset value (withFrame state (patch edit₃ state)))
          fun () => pure .next) = _
      rw [stored_frame]
      simp [store, State.read, receiver, index, Outcome.resume]

private theorem staged_unpack_error (program : Program) (available : List DeclarationId) (state : State)
    (edits : Edits) (clean : noPrivateSlots state) (rhs : Value) (loaded : edits.lookup saved = some (some rhs))
    (error : Error) (unpacked : unpackValue 2 rhs state = .error error state) :
    denoteBody program available (.assignTargetExpr (.unpack [firstSlot, secondSlot]) (readOperand saved))
      (patch edits state) = .error error (patch edits state) := by
  rw [unpack_read _ _ _ _ _ _ (patch_read_found _ _ _ _ (clean _ (private_pattern _ _)) loaded)]
  have same : unpackValue 2 rhs (patch edits state) = .error error (patch edits state) := by
    have eq := unpack_with_frame 2 rhs state (patch edits state)
    rw [unpacked] at eq
    exact eq
  rw [bindTarget.eq_def]
  change Outcome.resume (Outcome.resume (unpackValue 2 rhs (patch edits state))
    (bindTargets [.name firstSlot, .name secondSlot])) (fun () => pure Flow.next) = _
  rw [same]
  rfl

private theorem staged_unpack_ok (program : Program) (available : List DeclarationId) (state : State)
    (edits : Edits) (clean : noPrivateSlots state) (rhs : Value) (loaded : edits.lookup saved = some (some rhs))
    (first second : Value) (unpacked : unpackValue 2 rhs state = .ok [first, second] state) :
    denoteBody program available (.assignTargetExpr (.unpack [firstSlot, secondSlot]) (readOperand saved))
      (patch edits state) =
      .ok .next (patch ((secondSlot, some second) :: (firstSlot, some first) :: edits) state) := by
  rw [unpack_read _ _ _ _ _ _ (patch_read_found _ _ _ _ (clean _ (private_pattern _ _)) loaded)]
  have same : unpackValue 2 rhs (patch edits state) = .ok [first, second] (patch edits state) := by
    have eq := unpack_with_frame 2 rhs state (patch edits state)
    rw [unpacked] at eq
    exact eq
  rw [bindTarget.eq_def]
  change Outcome.resume (Outcome.resume (unpackValue 2 rhs (patch edits state))
    (bindTargets [.name firstSlot, .name secondSlot])) (fun () => pure Flow.next) = _
  rw [same]
  simp only [Outcome.resume, bindTargets, bindTarget]
  rw [private_write _ _ _ _ (clean _ (private_pattern _ _)),
    private_write _ _ _ _ (clean _ (private_pattern _ _))]
  rfl

private theorem store_fields (plan : Plan) (value : Value) (state final : State)
    (done : (store plan value state).resume (fun () => pure Flow.next) = .ok .next final ∨
      ∃ error, (store plan value state).resume (fun () => pure Flow.next) = .error error final) :
    final.slots = state.slots ∧ final.bindings = state.bindings := by
  unfold store at done
  cases receiver : state.bindingValue plan.receiver with
  | error error =>
    simp [State.read, receiver, Outcome.resume] at done
    obtain ⟨_, _, rfl⟩ := done
    exact ⟨rfl, rfl⟩
  | ok collection =>
    cases index : state.bindingValue plan.index with
    | error error =>
      simp [State.read, receiver, index, Outcome.resume] at done
      obtain ⟨_, _, rfl⟩ := done
      exact ⟨rfl, rfl⟩
    | ok offset =>
      cases write : writeIndex collection offset value state with
      | ok result next =>
        cases result
        simp [State.read, receiver, index, Outcome.resume, write, pure, EStateM.pure] at done
        subst final
        exact write_frame (error := .indexTarget) (.inl write)
      | error error next =>
        simp [State.read, receiver, index, Outcome.resume, write] at done
        obtain ⟨_, _, rfl⟩ := done
        exact write_frame (successValue := ()) (.inr write)

private theorem leafCode_eq (program : Program) (available : List DeclarationId) (plan : Plan)
    (code : Body) (same : code = plan.code) (state : State) (legal : plan.Legal)
    (clean : noPrivateSlots state) {out : Outcome Flow} (runs : Runs plan state out) :
    denoteBody program available code state = out := by
  subst code
  let saveEdits : Edits := [(saved, none)]
  have free (depth index : Nat) : state.slots (patternSlot depth index) = none :=
    clean _ (private_pattern _ _)
  have clearSaved : enterTemporaryBindings [saved] state = patch saveEdits state :=
    clear_eq _ _ (by simp [free])
  have outside : plan.rhs ∉ keys saveEdits := private_outside _ _ (legal _ (by simp))
    (edit_private _ _ _ (private_pattern _ _) (by simp [keys]))
  have right := patch_read _ _ outside state
  have phase := assignPattern_phases program available
    (.sequence [.name plan.destination, .subscript (readOperand plan.receiver) (readOperand plan.index)])
    (.plain (readOperand plan.rhs)) directStages state
  rw [Plan.code, denoteBody, phase, clearSaved]
  simp only [Expression.compile, directStages]
  rw [assign_read]
  simp only [State.read, right]
  cases runs with
  | @rhsError error failed =>
    simp only [failed, Outcome.resume]
    have restore := (restore_patch [saved] state state saveEdits
      (by simp [keys, saveEdits]) rfl (by intros; rfl) (.error error state)).2 error rfl
    rw [restore]
  | @unpackError rhs error evaluated unpacked =>
    simp only [evaluated, Outcome.resume]
    let root : Edits := (saved, some rhs) :: saveEdits
    have wrote := private_write saveEdits state saved rhs (free _ _)
    rw [wrote]
    simp only [AssignmentPattern.code]
    rw [denoteBody]
    change Outcome.resume (restoreTemporaryBindings [saved] state
      (restoreTemporaryBindings [firstSlot, secondSlot] (patch root state)
        (denoteBody program available _ (enterTemporaryBindings [firstSlot, secondSlot] (patch root state))))) _ = _
    have clearChildren := clear_eq [firstSlot, secondSlot] (patch root state) (by simp [free, patch])
    rw [clearChildren, ← patch_append, denoteBody]
    have h := staged_unpack_error program available state (clear [firstSlot, secondSlot] ++ root)
      clean rhs (by simp [clear, root, List.lookup_cons]) error ((unpacksValue_iff_unpackValue _ _ _ _).mp unpacked)
    simp only [readSaved, readOperand, List.length_cons, List.length_nil,
      show (List.range (0 + 1 + 1)).map (patternSlot 1) = [firstSlot, secondSlot] from rfl] at h ⊢
    rw [h]
    simp only [Outcome.resume]
    rw [patch_append]
    rw [(restore_patch [firstSlot, secondSlot] (patch root state) (patch root state)
      (clear [firstSlot, secondSlot]) (by simp [clear, keys]) rfl (by intros; rfl)
      (.error error (patch root state))).2 _ rfl]
    rw [(restore_patch [saved] state state root (by simp [keys, root, saveEdits]) rfl
      (by intros; rfl) (.error error state)).2 _ rfl]
  | @leaves rhs first second evaluated unpacked =>
    simp only [evaluated, Outcome.resume]
    let root : Edits := (saved, some rhs) :: saveEdits
    rw [private_write saveEdits state saved rhs (free _ _)]
    simp only [AssignmentPattern.code]
    rw [denoteBody]
    change Outcome.resume (restoreTemporaryBindings [saved] state
      (restoreTemporaryBindings [firstSlot, secondSlot] (patch root state)
        (denoteBody program available _ (enterTemporaryBindings [firstSlot, secondSlot] (patch root state))))) _ = _
    rw [clear_eq [firstSlot, secondSlot] (patch root state) (by simp [free, patch]), ← patch_append, denoteBody]
    let unpackedEdits : Edits := clear [firstSlot, secondSlot] ++ root
    let writes : Edits := [(secondSlot, some second), (firstSlot, some first)] ++ clear [firstSlot, secondSlot]
    let all : Edits := writes ++ root
    have h := staged_unpack_ok program available state unpackedEdits clean rhs (by simp [unpackedEdits, clear, root, List.lookup_cons]) first second
      ((unpacksValue_iff_unpackValue _ _ _ _).mp unpacked)
    simp only [readSaved, readOperand, List.length_cons, List.length_nil,
      show (List.range (0 + 1 + 1)).map (patternSlot 1) = [firstSlot, secondSlot] from rfl] at h ⊢
    rw [h]
    simp only [Outcome.resume, AssignmentPattern.childCode, AssignmentPattern.code, readSaved]
    rw [denoteBody]
    have assignment := assign_read program available (patch ((secondSlot, some second) :: (firstSlot, some first) :: unpackedEdits) state) plan.destination firstSlot
    simp only [readOperand] at assignment
    rw [assignment]
    rw [show ((secondSlot, some second) :: (firstSlot, some first) :: unpackedEdits : Edits) = all from rfl]
    have firstRead := patch_read_found all firstSlot first state (free _ _) (by simp [all, writes, List.lookup_cons])
    simp only [State.read, firstRead, Outcome.resume]
    have allPrivate : ∀ key ∈ keys all, key.name.toList.head? = some '$' := by
      simp [all, writes, root, saveEdits, keys, clear, private_pattern]
    rw [write_patch all state plan.destination first (private_outside _ _ (legal _ (by simp)) allPrivate)]
    let named := state.write plan.destination first
    have nameFields := write_fields state plan.destination first
    have namedClean : noPrivateSlots named := by
      unfold noPrivateSlots named
      rw [nameFields.1]
      exact clean
    have stages := staged_store program available plan legal named all namedClean allPrivate second (by simp [all, writes])
    simp only [readOperand, directStages, named] at stages
    rw [denoteBody]
    simp only [Nat.zero_add]
    rw [stages]
    have pass (next : State) : denoteBody program available (.total (.atomic .pass)) next = .ok .next next :=
      (denote_total _ _ _ _).trans ((runs_iff_denoteSuite _ _ _).mp (.atomic Eval.pass))
    cases finished : store plan second named with
    | error error final =>
      have frame := store_fields plan second named final (.inr ⟨error, by rw [finished]; rfl⟩)
      simp only [Outcome.resume, mapState]
      rw [patch_append]
      have resetInner := (restore_patch [firstSlot, secondSlot] (patch root state) (patch root final) writes
        (by simp [keys, writes, clear]) (nameFields.1.symm.trans frame.1.symm)
        (by
          intro key present
          change (root.lookup key).getD (state.bindings key) = (root.lookup key).getD (final.bindings key)
          rw [frame.2]
          apply congrArg ((root.lookup key).getD)
          exact (nameFields.2 key (by
            intro same
            exact (legal plan.destination (by simp)) (by
              rcases List.mem_cons.mp present with rfl | tail
              · exact same ▸ private_pattern _ _
              · cases List.mem_singleton.mp tail; exact same ▸ private_pattern _ _))).symm)
        (.error error (patch root final))).2 _ rfl
      rw [resetInner]
      have resetOuter := (restore_patch [saved] state final root (by simp [keys, root, saveEdits])
        (nameFields.1.symm.trans frame.1.symm) (by
          intro key member
          cases List.mem_singleton.mp member
          rw [frame.2]
          exact (nameFields.2 _ (by
            intro same
            exact (legal plan.destination (by simp)) (same ▸ private_pattern _ _))).symm)
        (.error error final)).2 _ rfl
      rw [resetOuter]
    | ok result final =>
      cases result
      have frame := store_fields plan second named final (.inl (by rw [finished]; rfl))
      simp [Outcome.resume, mapState, pure, EStateM.pure, pass]
      rw [patch_append]
      rw [(restore_patch [firstSlot, secondSlot] (patch root state) (patch root final) writes
        (by simp [keys, writes, clear]) (nameFields.1.symm.trans frame.1.symm)
        (by
          intro key present
          change (root.lookup key).getD (state.bindings key) = (root.lookup key).getD (final.bindings key)
          rw [frame.2]
          apply congrArg ((root.lookup key).getD)
          exact (nameFields.2 key (by
            intro same
            exact (legal plan.destination (by simp)) (by
              rcases List.mem_cons.mp present with rfl | tail
              · exact same ▸ private_pattern _ _
              · cases List.mem_singleton.mp tail; exact same ▸ private_pattern _ _))).symm)
        (.ok .next (patch root final))).1 _ rfl]
      rw [(restore_patch [saved] state final root (by simp [keys, root, saveEdits])
        (nameFields.1.symm.trans frame.1.symm) (by
          intro key member
          cases List.mem_singleton.mp member
          rw [frame.2]
          exact (nameFields.2 _ (by
            intro same
            exact (legal plan.destination (by simp)) (same ▸ private_pattern _ _))).symm)
        (.ok .next final)).1 _ rfl]
      exact return_read _ _ _ _

theorem leaf_denotes (program : Program) (available : List DeclarationId) (plan : Plan)
    (state : State) (legal : plan.Legal) (clean : noPrivateSlots state)
    {out : Outcome Flow} (runs : Runs plan state out) :
    denoteBody program available plan.code state = out :=
  leafCode_eq program available plan _ rfl state legal clean runs

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf
