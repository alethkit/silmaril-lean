module

public import Silmaril.Courses.Cambridge.L2.Concrete

/-! # A byte grammar for Cambridge L1

The L1 syntax of Sewell (2025–26), §2.3, pp. 29–30, is the imperative
fragment of the shared reader. The fragment check applies at every node,
leaving the existing L1 and L2 semantic datatypes as they are. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.Concrete

/-- Use the common concrete spelling for an L1 tree. -/
def toRaw : Expr → L2.RawExpr
  | .int n => .int n
  | .bool b => .bool b
  | .binary left op right => .binary (toRaw left) op (toRaw right)
  | .cond test yes no => .cond (toRaw test) (toRaw yes) (toRaw no)
  | .assign name value => .assign name (toRaw value)
  | .deref name => .deref name
  | .skip => .skip
  | .seq left right => .seq (toRaw left) (toRaw right)
  | .loop test body => .loop (toRaw test) (toRaw body)

def ofRaw : L2.RawExpr → Option Expr
  | .int n => some (.int n)
  | .bool b => some (.bool b)
  | .binary left op right => do
      return .binary (← ofRaw left) op (← ofRaw right)
  | .cond test yes no => do
      return .cond (← ofRaw test) (← ofRaw yes) (← ofRaw no)
  | .assign name value => do return .assign name (← ofRaw value)
  | .deref name => some (.deref name)
  | .skip => some .skip
  | .seq left right => do return .seq (← ofRaw left) (← ofRaw right)
  | .loop test body => do return .loop (← ofRaw test) (← ofRaw body)
  | .var _ | .lam .. | .app .. | .letE .. | .letRecFun .. => none

theorem ofRaw_toRaw (expr : Expr) : ofRaw (toRaw expr) = some expr := by
  induction expr <;> simp [toRaw, ofRaw, *]

def parse (bytes : ByteArray) : Option Expr := L2.Concrete.parse bytes >>= ofRaw

def Parses (bytes : ByteArray) (term : Expr) : Prop := parse bytes = some term

def NamesOk (term : Expr) : Prop := L2.Concrete.NamesOk (toRaw term)

abbrev SourceExpr := {term : Expr // NamesOk term}

def print (term : SourceExpr) : ByteArray :=
  L2.Concrete.print ⟨toRaw term.val, term.property⟩

/-- The complete byte parser recovers every canonically printed L1 source AST. -/
theorem parse_print (term : SourceExpr) : parse (print term) = some term.val := by
  unfold parse print
  rw [L2.Concrete.parse_print]
  exact ofRaw_toRaw term.val

theorem print_injective : Function.Injective print := by
  intro left right h
  apply Subtype.ext
  exact Option.some.inj ((parse_print left).symm.trans ((congrArg parse h).trans (parse_print right)))

theorem parses_print (term : SourceExpr) : Parses (print term) term.val := parse_print term

def toType : Ty → L2.Ty
  | .int => .int
  | .bool => .bool
  | .unit => .unit

def parseType (bytes : ByteArray) : Option Ty := do
  match ← L2.Concrete.parseType bytes with
  | .int => some .int
  | .bool => some .bool
  | .unit => some .unit
  | .arr .. => none

def printType (type : Ty) : ByteArray := L2.Concrete.printType (toType type)

theorem parseType_printType (type : Ty) : parseType (printType type) = some type := by
  unfold parseType printType
  rw [L2.Concrete.parseType_printType]
  cases type <;> rfl

theorem printType_injective : Function.Injective printType := by
  intro left right h
  exact Option.some.inj ((parseType_printType left).symm.trans
    ((congrArg parseType h).trans (parseType_printType right)))

end Silmaril.Courses.Cambridge.L1.Concrete
