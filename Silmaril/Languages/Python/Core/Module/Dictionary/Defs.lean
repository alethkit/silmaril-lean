module

public import Silmaril.Languages.Python.Core.Module.TupleDispatch.Defs

/-! # Read-only Python dictionaries built from exact displays -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Module.Dictionary

abbrev Atom := TupleDispatch.Element
abbrev Entry := Atom × Atom

/-- Replacing an equal key keeps its original tag and position. -/
def insert (entry : Entry) : List Entry → List Entry
  | [] => [entry]
  | first :: rest =>
    if first.1.equal entry.1 then (first.1, entry.2) :: rest
    else first :: insert entry rest

def build (display : List Entry) : List Entry :=
  display.foldl (fun entries entry => insert entry entries) []

structure Object where
  address : Nat
  entries : List Entry
  deriving DecidableEq, Repr

inductive Argument where
  | literal (value : Atom)
  | global (name : String)

structure Get where
  receiver : String
  key : Argument
  fallback : Argument

inductive ReadValue where
  | atom (value : Atom)
  | object (value : Object)
  | unsupported

inductive Failure where
  | missingName (name : String)
  | unsupported

def readName (globals : String → Option ReadValue) (name : String) :
    Except Failure ReadValue :=
  (globals name).elim (.error (.missingName name)) .ok

def Argument.read (globals : String → Option ReadValue) : Argument → Except Failure ReadValue
  | .literal value => .ok (.atom value)
  | .global name => readName globals name

/-- The live receiver selects the stock method before argument preparation.
Even on a hit the default is read before lookup. The object table validates
the handle and supplies the contents used by the lookup. -/
def Get.eval (test : Get) (globals : String → Option ReadValue) (resolve : Object → Option (List Entry)) :
    Except Failure Atom := do
  let .object object ← readName globals test.receiver | throw .unsupported
  let some entries := resolve object | throw .unsupported
  let key ← test.key.read globals
  let fallback ← test.fallback.read globals
  let .atom needle := key | throw .unsupported
  let .atom defaultValue := fallback | throw .unsupported
  return Core.Module.dictionaryGet TupleDispatch.Element.equal entries needle defaultValue

end Silmaril.Languages.Python.Core.Module.Dictionary
