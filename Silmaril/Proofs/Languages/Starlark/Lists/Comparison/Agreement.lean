module

public import Silmaril.Languages.Starlark.Lists.Comparison.Operational.Defs
import Silmaril.Languages.Starlark.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.Comparison

open Silmaril.Languages
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Comparison

theorem scans_iff_scan {α : Type} {tests : α → Except Error Bool → Prop}
    {test : α → Except Error Bool} (agrees : ∀ item out, tests item out ↔ test item = out)
    (decisive : Bool) (items : List α) (out : Except Error Bool) :
    Scans tests decisive items out ↔ scan test decisive items = out := by
  constructor
  · intro runs
    induction runs with
    | empty => rfl
    | stopped hit => simp [scan, (agrees _ _).mp hit]
    | failed fails => simp [scan, (agrees _ _).mp fails]
    | continued misses _ ih =>
      cases decisive <;> simpa [scan, (agrees _ _).mp misses] using ih
  · intro runs
    subst out
    induction items with
    | nil => exact .empty
    | cons item rest ih =>
      rw [scan]
      cases got : test item with
      | error error => exact .failed ((agrees _ _).mpr got)
      | ok flag =>
        by_cases stops : flag = decisive
        · subst flag
          simpa using Scans.stopped (rest := rest) ((agrees _ _).mpr got)
        · have misses : flag = !decisive := by
            cases flag <;> cases decisive <;> simp_all
          subst flag
          simpa [stops] using Scans.continued ((agrees _ _).mpr got) ih

private theorem scalar_result (left right : Starlark.Value) :
    Starlark.applyBinary .eq left right = .ok (.bool (scalarEqual left right)) := by
  cases order : left.orderedCompare right <;>
    simp [Starlark.applyBinary, Starlark.comparisonResult, scalarEqual, order]

theorem equalAt_iff (heap : Heap) (depth : Nat) (left right : Value)
    (out : Except Error Bool) :
    EqualAt heap depth left right out ↔ equalAt heap depth left right = out := by
  induction depth generalizing left right out with
  | zero => exact eq_comm
  | succ depth ih =>
    rw [EqualAt, equalAt]
    constructor
    · intro runs
      cases runs with
      | scalar route compares =>
        have computed := ((Starlark.compares_iff_applyBinary ..).mp compares).2
        rw [scalar_result] at computed
        simpa [route] using computed
      | string route => simp [route]
      | different route | unsupported route => simp [route]
      | leftError route read => simp [route, read, Except.bind, bind]
      | rightError route first second => simp [route, first, second, Except.bind, bind]
      | lengthMismatch route first second lengths =>
        simp [route, first, second, lengths, Except.bind, bind, pure, Except.pure]
      | fields route first second lengths runs =>
        simpa [route, first, second, lengths, Except.bind, bind] using
          (scans_iff_scan (fun (pair : Value × Value) => ih pair.1 pair.2) ..).mp runs
    · intro runs
      subst out
      cases route : Pair.ofValues left right with
      | scalars a b =>
        exact .scalar route ((Starlark.compares_iff_applyBinary ..).mpr ⟨rfl, scalar_result a b⟩)
      | strings a b => exact .string route
      | different => exact .different route
      | unsupported => exact .unsupported route
      | sequences kind a b =>
        cases first : kind.elements heap a with
        | error error =>
          simpa [first, Except.bind, bind] using
            EqualStep.leftError (next := EqualAt heap depth) route first
        | ok xs =>
          cases second : kind.elements heap b with
          | error error =>
            simpa [first, second, Except.bind, bind] using
              EqualStep.rightError (next := EqualAt heap depth) route first second
          | ok ys =>
            by_cases lengths : xs.length = ys.length
            · simpa [first, second, lengths, Except.bind, bind] using
                EqualStep.fields route first second lengths
                  ((scans_iff_scan (fun (pair : Value × Value) => ih pair.1 pair.2) ..).mpr rfl)
            · simpa [first, second, lengths, Except.bind, bind, pure, Except.pure] using
                EqualStep.lengthMismatch (next := EqualAt heap depth) route first second lengths

theorem containsAt_iff (heap : Heap) (depth : Nat) (needle target : Value)
    (out : Except Error Bool) :
    ContainsAt heap depth needle target out ↔ containsAt heap depth needle target = out := by
  constructor
  · intro runs
    cases runs with
    | unsupported route => simp [containsAt, route]
    | readError route read => simp [containsAt, route, read, Except.bind, bind]
    | fields route read runs =>
      simpa [containsAt, route, read, Except.bind, bind] using
        (scans_iff_scan (fun field => equalAt_iff heap depth field needle) ..).mp runs
  · intro runs
    subst out
    cases route : SequenceKind.locate target with
    | none =>
      simpa [containsAt, route] using
        ContainsAt.unsupported (heap := heap) (depth := depth) (needle := needle) route
    | some sequence =>
      obtain ⟨kind, address⟩ := sequence
      cases read : kind.elements heap address with
      | error error =>
        simpa [containsAt, route, read, Except.bind, bind] using
          ContainsAt.readError (depth := depth) (needle := needle) route read
      | ok fields =>
        simpa [containsAt, route, read, Except.bind, bind] using
          ContainsAt.fields route read
            ((scans_iff_scan (fun field => equalAt_iff heap depth field needle) ..).mpr rfl)

theorem tests_iff_evaluate (heap : Heap) (left right : Value) (op : ComparisonOp)
    (out : Except Error Bool) :
    Tests heap left right op out ↔ evaluate heap op left right = out := by
  have eq := equalAt_iff heap defaultDepth left right
  have mem := containsAt_iff heap defaultDepth left right
  constructor
  · intro runs
    cases runs with
    | eq runs => exact (eq _).mp runs
    | ne runs => simp only [evaluate, (eq _).mp runs]
    | mem runs => exact (mem _).mp runs
    | notMem runs => simp only [evaluate, (mem _).mp runs]
  · intro runs
    subst out
    cases op with
    | eq => exact .eq ((eq _).mpr rfl)
    | ne => exact .ne ((eq _).mpr rfl)
    | mem => exact .mem ((mem _).mpr rfl)
    | notMem => exact .notMem ((mem _).mpr rfl)

end Silmaril.Proofs.Languages.Starlark.Lists.Comparison
