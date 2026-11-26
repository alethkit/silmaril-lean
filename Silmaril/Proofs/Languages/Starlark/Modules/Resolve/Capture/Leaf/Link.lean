module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Lists (State Capture)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve (requiredSignature)
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf
open Silmaril.Languages.Starlark.Functions

private theorem reads_match {block : LexicalBlock} {name : String} {binding : Binding}
    {code : Lowering.Expr} {reads : List Binding}
    (chosen : ReadResolves block name (readOperand binding) [binding])
    (related : OperandResolves block (.scalar (.read name)) code reads) :
    code = readOperand binding := by
  cases related with
  | read _ found =>
    unfold readOperand at chosen ⊢
    cases chosen <;> cases found <;> simp_all

private theorem target_matches {block : LexicalBlock} {name receiver index : String}
    {collection offset : Binding} {pattern : Comprehensions.AssignmentPattern}
    {names : List String} {reads : List Binding}
    (receiverRead : ReadResolves block receiver (readOperand collection) [collection])
    (indexRead : ReadResolves block index (readOperand offset) [offset])
    (resolved : TargetResolves block .local
      (.tuple [.scalar (.read name), .index (.scalar (.read receiver)) (.scalar (.read index))])
      pattern names reads) :
    pattern = .sequence [.name (fileSlot name), .subscript (readOperand collection) (readOperand offset)] := by
  obtain ⟨shape, shapeRules, compiled⟩ := resolved
  cases shapeRules with
  | tuple children =>
    cases children with
    | cons first children =>
      cases first
      cases children with
      | cons second children =>
        cases second
        cases children
        cases compiled with
        | sequence items =>
          cases items with
          | cons first items =>
            cases first
            cases items with
            | cons second items =>
              cases items
              cases second with
              | subscript receiverCode indexCode =>
                rw [reads_match receiverRead receiverCode, reads_match indexRead indexCode]
                rfl

theorem code_of_lexical {block : LexicalBlock} {body : MixedBody} {plan : Plan}
    {code : Body} (compiled : LeafCode block body code) (lexical : Resolves block body plan) :
    code = plan.code := by
  cases lexical with
  | reads destination rhs receiver index returned right collection offset result rhsRead recvRead indexRead returnRead =>
    cases compiled with
    | linked assignment returnCode reads resolved returnedCode =>
      have target := target_matches recvRead indexRead resolved.targetResolves
      have returnEqual := reads_match returnRead returnedCode
      rcases assignment with ⟨pattern, value, names, rhsReads, targetReads⟩
      have rhsEqual : value = .plain (readOperand right) := by
        have elaborated := resolved.rhsResolves
        cases elaborated with
        | plain related => congr 1; exact reads_match rhsRead related
      unfold Plan.code
      dsimp only
      dsimp only at target
      rw [target, rhsEqual, returnEqual]

theorem activate_no_private (state : State) (frame : Forwarding.Frame) (captures : List Capture)
    (arguments : List (Binding × Silmaril.Languages.Starlark.Lists.Value))
    (owned : ∀ name ∈ frame.owned, name.toList.head? ≠ some '$')
    (free : ∀ capture ∈ captures, capture.binding.name.toList.head? ≠ some '$') :
    noPrivateSlots (activate state frame.declaration captures arguments) := by
  intro name secret
  have noCapture : capturedSlots captures name = none := by
    unfold capturedSlots
    cases found : captures.find? (fun entry => entry.binding == name) with
    | none => rfl
    | some capture =>
      have tested : (capture.binding == name) = true :=
        List.find?_some (p := fun entry : Capture => entry.binding == name) found
      have equal := beq_iff_eq.mp tested
      exact (free capture (List.mem_of_find?_eq_some found) (equal ▸ secret)).elim
  have undisclosed : name ∉ frame.declaration.signature.slots ++ frame.declaration.locals := by
    intro member
    have slots : frame.declaration.signature.slots ++ frame.declaration.locals = frame.owned.map fileSlot := by
      simp [Forwarding.Frame.declaration, Forwarding.Frame.owned, requiredSignature, Signature.slots, Signature.named]
    rw [slots] at member
    obtain ⟨source, declared, equal⟩ := List.mem_map.mp member
    exact owned source declared (by simpa [fileSlot, ← equal] using secret)
  have allocate (names : List Binding) (state : State) (outside : name ∉ names) (blank : state.slots name = none) :
      (names.foldl State.allocateSlot state).slots name = none := by
    induction names generalizing state with
    | nil => exact blank
    | cons first rest ih =>
      simp only [List.mem_cons, not_or] at outside
      exact ih _ outside.2 (by simp [State.allocateSlot, outside.1, blank])
  have write (entries : List (Binding × Silmaril.Languages.Starlark.Lists.Value)) (state : State)
      (blank : state.slots name = none) :
      (entries.foldl (fun next (binding, value) => next.write binding value) state).slots name = none := by
    induction entries generalizing state with
    | nil => exact blank
    | cons first rest ih =>
      apply ih
      change (state.write first.1 first.2).slots name = none
      unfold State.write
      split <;> try exact blank
      split <;> exact blank
  exact write _ _ (allocate _ _ undisclosed noCapture)

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf
