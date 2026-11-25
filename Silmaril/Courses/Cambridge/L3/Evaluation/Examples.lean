module

import Silmaril.Courses.Cambridge.L3.Evaluation
meta import Silmaril.Courses.Cambridge.L3.Evaluation
meta import Silmaril.Courses.Cambridge.L3.Syntax
meta import Silmaril.Courses.Cambridge.L3.Store

/-! Executable checks for the Exercise 31 pipeline and its diagnostic outcomes. -/

namespace Silmaril.Courses.Cambridge.L3

private def integer (n : Int) : Value := ⟨.int n, .int n⟩

-- Strict let allocates at the existing reducer's chosen address.
#guard match evaluate "let r:(int ref)=ref 7 in !r".toUTF8 ∅ ∅ 3 with
  | .evaluated .int (.returned ⟨.int 7, _⟩ final) =>
      match final.lookup 1 with
      | some ⟨.int 7, _⟩ => true
      | _ => false
  | _ => false

-- Parse, infer, and evaluate record projection and the selected sum branch.
#guard match evaluate
    "match (inr {p=(2,true)}:(int+{p:(int*bool)})) with inl (x:int)->x | inr (y:{p:(int*bool)})->fst (y.p)".toUTF8
    ∅ ∅ 8 with
  | .evaluated .int (.returned ⟨.int 2, _⟩ _) => true
  | _ => false

#guard match evaluate "let rec f:int→int=(fun x:int→(if x>=1 then (f (x+-1)) else 12)) in (f 2)".toUTF8
    ∅ ∅ 50 with
  | .evaluated .int (.returned ⟨.int 12, _⟩ _) => true
  | _ => false

#guard match evaluate "let rec f:int→int=(fun x:int→(f x)) in (f 0)".toUTF8 ∅ ∅ 10 with
  | .evaluated .int (.outOfFuel _) => true
  | _ => false

#guard match evaluate "42".toUTF8 ∅ ∅ 0 with
  | .evaluated .int (.returned ⟨.int 42, _⟩ _) => true
  | _ => false

#guard match evaluate "let r:(int ref)=ref 7 in !r".toUTF8 ∅ ∅ 0 with
  | .evaluated .int (.outOfFuel _) => true
  | _ => false

#guard match evaluate (ByteArray.mk #[0xc0, 0xaf]) ∅ ∅ 1 with
  | .parseError => true
  | _ => false

#guard match evaluate "(!l)".toUTF8 ∅ ∅ 1 with
  | .expressionTypeError => true
  | _ => false

#guard match evaluate "{p=true}.q".toUTF8 ∅ ∅ 1 with
  | .expressionTypeError => true
  | _ => false

-- Record types compare their ordered labels even when the field types coincide.
#guard match evaluate "let x:{p:int,q:int}={q=1,p=2} in x".toUTF8 ∅ ∅ 1 with
  | .expressionTypeError => true
  | _ => false

#guard match evaluate "(!l)".toUTF8 ((∅ : LocTypes).insert 0 .int) ∅ 1 with
  | .storeTypeError => true
  | _ => false

#guard match evaluate "(!l)".toUTF8 ∅ ((∅ : Store).insert 0 (integer 7)) 1 with
  | .storeTypeError => true
  | _ => false

#guard match evaluate "(!l)".toUTF8 ((∅ : LocTypes).insert 0 .bool)
    ((∅ : Store).insert 0 (integer 7)) 1 with
  | .storeTypeError => true
  | _ => false

#guard match evaluate "(!l)".toUTF8 ((∅ : LocTypes).insert 0 .int)
    ((∅ : Store).insert 0 (integer 7)) 1 with
  | .evaluated .int (.returned ⟨.int 7, _⟩ _) => true
  | _ => false

-- The raw runner can get stuck. The validated surface workflow cannot.
#guard match runFuel 0 ⟨.deref (.loc 0), ∅⟩ with
  | .stuck _ => true
  | _ => false

-- A function cell may refer to itself through a location of known type.
private def cyclicClosure : Value :=
  ⟨.lam .int (.app (.deref (.loc 0)) (.bvar 0)), .lam _ _⟩

#guard checkStore ((∅ : LocTypes).insert 0 (.arr .int .int))
    ((∅ : Store).insert 0 cyclicClosure)

end Silmaril.Courses.Cambridge.L3
