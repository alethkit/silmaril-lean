module

public import Silmaril.Languages.Starlark.Lists.Comparison.Defs
public import Silmaril.Languages.Starlark.Comparison.Operational.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists.Comparison

/-- An ordered scan records the decisive item or first reached error. -/
inductive Scans {α : Type} (tests : α → Except Error Bool → Prop) (decisive : Bool) :
    List α → Except Error Bool → Prop where
  | empty : Scans tests decisive [] (.ok (!decisive))
  | stopped {item : α} {rest : List α} :
      tests item (.ok decisive) → Scans tests decisive (item :: rest) (.ok decisive)
  | failed {item : α} {rest : List α} {error : Error} :
      tests item (.error error) → Scans tests decisive (item :: rest) (.error error)
  | continued {item : α} {rest : List α} {out : Except Error Bool} :
      tests item (.ok (!decisive)) → Scans tests decisive rest out →
      Scans tests decisive (item :: rest) out

/-- One nonzero level of comparison. Only sequences of the same kind and
length scan fields. Their addresses do not determine equality. -/
inductive EqualStep (heap : Heap) (next : Value → Value → Except Error Bool → Prop)
    (left right : Value) : Except Error Bool → Prop where
  | scalar {a b : Starlark.Value} {flag : Bool} :
      Pair.ofValues left right = .scalars a b → Starlark.Compares .eq a b (.ok (.bool flag)) →
      EqualStep heap next left right (.ok flag)
  | string {a b : String} :
      Pair.ofValues left right = .strings a b →
      EqualStep heap next left right (.ok (decide (a = b)))
  | different : Pair.ofValues left right = .different → EqualStep heap next left right (.ok false)
  | unsupported : Pair.ofValues left right = .unsupported →
      EqualStep heap next left right (.error (.comparisonType left right))
  | leftError {kind : SequenceKind} {a b : Address} {error : Error} :
      Pair.ofValues left right = .sequences kind a b → kind.elements heap a = .error error →
      EqualStep heap next left right (.error error)
  | rightError {kind : SequenceKind} {a b : Address} {xs : List Value} {error : Error} :
      Pair.ofValues left right = .sequences kind a b →
      kind.elements heap a = .ok xs → kind.elements heap b = .error error →
      EqualStep heap next left right (.error error)
  | lengthMismatch {kind : SequenceKind} {a b : Address} {xs ys : List Value} :
      Pair.ofValues left right = .sequences kind a b →
      kind.elements heap a = .ok xs → kind.elements heap b = .ok ys → xs.length ≠ ys.length →
      EqualStep heap next left right (.ok false)
  | fields {kind : SequenceKind} {a b : Address} {xs ys : List Value} {out : Except Error Bool} :
      Pair.ofValues left right = .sequences kind a b →
      kind.elements heap a = .ok xs → kind.elements heap b = .ok ys → xs.length = ys.length →
      Scans (fun pair => next pair.1 pair.2) false (xs.zip ys) out →
      EqualStep heap next left right out

def EqualAt (heap : Heap) : Nat → Value → Value → Except Error Bool → Prop
  | 0, _, _, out => out = .error .comparisonDepth
  | depth + 1, left, right, out => EqualStep heap (EqualAt heap depth) left right out

inductive ContainsAt (heap : Heap) (depth : Nat) (needle target : Value) : Except Error Bool → Prop where
  | unsupported : SequenceKind.locate target = none →
      ContainsAt heap depth needle target (.error (.membershipTarget target))
  | readError {kind : SequenceKind} {address : Address} {error : Error} :
      SequenceKind.locate target = some (kind, address) → kind.elements heap address = .error error →
      ContainsAt heap depth needle target (.error error)
  | fields {kind : SequenceKind} {address : Address} {xs : List Value} {out : Except Error Bool} :
      SequenceKind.locate target = some (kind, address) → kind.elements heap address = .ok xs →
      Scans (fun field => EqualAt heap depth field needle) true xs out →
      ContainsAt heap depth needle target out

/-- Operator rules yield either a Boolean or the error from the reached test. -/
inductive Tests (heap : Heap) (left right : Value) : ComparisonOp → Except Error Bool → Prop where
  | eq {out : Except Error Bool} :
      EqualAt heap defaultDepth left right out → Tests heap left right .eq out
  | ne {out : Except Error Bool} :
      EqualAt heap defaultDepth left right out → Tests heap left right .ne ((! ·) <$> out)
  | mem {out : Except Error Bool} :
      ContainsAt heap defaultDepth left right out → Tests heap left right .mem out
  | notMem {out : Except Error Bool} :
      ContainsAt heap defaultDepth left right out → Tests heap left right .notMem ((! ·) <$> out)

end Silmaril.Languages.Starlark.Lists.Comparison
