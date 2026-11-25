module

public import Silmaril.Courses.Cambridge.L3.Concrete.Proofs

/-! # L3 bytes with separate variable and label classes

Sewell §§5.2 and 5.5 distinguish the classes but leave their complete
spelling sets open. A classifier fixes the role of each identifier
for the whole input profile, including uses outside a binder's scope.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Concrete.Exact

inductive NameClass where
  | variable
  | label
  deriving DecidableEq

abbrev Classifier := String → NameClass

abbrev TypeIn (classify : Classifier) := TypeNames (fun name => classify name = .label)

abbrev ExprIn (classify : Classifier) :=
  ExprNames (fun name => classify name = .variable) (fun name => classify name = .label)

local notation "both" =>
  (fun {p q : Prop} (left : Decidable p) (right : Decidable q) => @instDecidableAnd p q left right)

def decideTypeIn (classify : Classifier) : (type : Ty) → Decidable (TypeIn classify type)
  | .int | .bool | .unit => isTrue trivial
  | .arr left right | .prod left right | .sum left right =>
      both (decideTypeIn classify left) (decideTypeIn classify right)
  | .ref contents => decideTypeIn classify contents
  | .record labels fields =>
      @Nat.decidableForallFin _ _ fun i =>
        both (inferInstanceAs (Decidable (classify (labels.label i) = .label)))
          (decideTypeIn classify (fields i))

def decideExprIn (classify : Classifier) : (term : RawExpr) → Decidable (ExprIn classify term)
  | .int _ | .bool _ | .skip | .loc _ => isTrue trivial
  | .var name => checkVar name
  | .assign left right | .binary left _ right | .seq left right | .loop left right
  | .app left right | .pair left right =>
      both (decideExprIn classify left) (decideExprIn classify right)
  | .deref value | .ref value | .fst value | .snd value => decideExprIn classify value
  | .cond test yes no =>
      both (decideExprIn classify test)
        (both (decideExprIn classify yes) (decideExprIn classify no))
  | .lam name type body =>
      both (checkVar name) (both (decideTypeIn classify type) (decideExprIn classify body))
  | .letE name type value body =>
      both (checkVar name) (both (decideTypeIn classify type)
        (both (decideExprIn classify value) (decideExprIn classify body)))
  | .letRecFun fn param domain codomain value body =>
      both (checkVar fn) (both (checkVar param) (both (decideTypeIn classify domain)
        (both (decideTypeIn classify codomain)
          (both (decideExprIn classify value) (decideExprIn classify body)))))
  | .inl value type | .inr value type =>
      both (decideExprIn classify value) (decideTypeIn classify type)
  | .matchSum value x typeX left y typeY right =>
      both (decideExprIn classify value) (both (checkVar x) (both (decideTypeIn classify typeX)
        (both (decideExprIn classify left) (both (checkVar y)
          (both (decideTypeIn classify typeY) (decideExprIn classify right))))))
  | .record labels fields =>
      @Nat.decidableForallFin _ _ fun i =>
        both (checkLabel (labels.label i)) (decideExprIn classify (fields i))
  | .project value label => both (decideExprIn classify value) (checkLabel label)
where
  checkVar (name : Var) : Decidable (classify name = .variable) := inferInstance
  checkLabel (name : Label) : Decidable (classify name = .label) := inferInstance

instance (classify : Classifier) (type : Ty) : Decidable (TypeIn classify type) :=
  decideTypeIn classify type

instance (classify : Classifier) (term : RawExpr) : Decidable (ExprIn classify term) :=
  decideExprIn classify term

def parse (classify : Classifier) (bytes : ByteArray) : Option RawExpr :=
  (Concrete.parse bytes).filter (fun term => decide (ExprIn classify term))

def parseType (classify : Classifier) (bytes : ByteArray) : Option Ty :=
  (Concrete.parseType bytes).filter (fun type => decide (TypeIn classify type))

def parseResolved (classify : Classifier) (bytes : ByteArray) : Option Expr :=
  (parse classify bytes).map (RawExpr.resolve [])

theorem parse_eq_some_iff {classify : Classifier} {bytes : ByteArray} {term : RawExpr} :
    parse classify bytes = some term ↔ Concrete.parse bytes = some term ∧ ExprIn classify term := by
  simp [parse, Option.filter_eq_some_iff]

theorem parseType_eq_some_iff {classify : Classifier} {bytes : ByteArray} {type : Ty} :
    parseType classify bytes = some type ↔
      Concrete.parseType bytes = some type ∧ TypeIn classify type := by
  simp [parseType, Option.filter_eq_some_iff]

/-- Canonical terms use spellable identifiers from the indicated classes. -/
abbrev SourceExpr (classify : Classifier) := {term : RawExpr // NamesOk term ∧ ExprIn classify term}

/-- Canonical types use spellable record labels from the label class. -/
abbrev SourceType (classify : Classifier) := {type : Ty // TypeNamesOk type ∧ TypeIn classify type}

def print {classify : Classifier} (term : SourceExpr classify) : ByteArray :=
  Concrete.print ⟨term.val, term.property.1⟩

def printType {classify : Classifier} (type : SourceType classify) : ByteArray :=
  Concrete.printType ⟨type.val, type.property.1⟩

theorem parse_print {classify : Classifier} (term : SourceExpr classify) :
    parse classify (print term) = some term.val :=
  parse_eq_some_iff.mpr ⟨Concrete.parse_print ⟨term.val, term.property.1⟩, term.property.2⟩

theorem parseType_printType {classify : Classifier} (type : SourceType classify) :
    parseType classify (printType type) = some type.val :=
  parseType_eq_some_iff.mpr
    ⟨Concrete.parseType_printType ⟨type.val, type.property.1⟩, type.property.2⟩

theorem parseResolved_print {classify : Classifier} (term : SourceExpr classify) :
    parseResolved classify (print term) = some (term.val.resolve []) := by
  simp [parseResolved, parse_print]

theorem print_injective (classify : Classifier) : Function.Injective (@print classify) := by
  intro left right same
  apply Subtype.ext
  exact Option.some.inj ((parse_print left).symm.trans
    ((congrArg (parse classify) same).trans (parse_print right)))

theorem printType_injective (classify : Classifier) : Function.Injective (@printType classify) := by
  intro left right same
  apply Subtype.ext
  exact Option.some.inj ((parseType_printType left).symm.trans
    ((congrArg (parseType classify) same).trans (parseType_printType right)))

end Silmaril.Courses.Cambridge.L3.Concrete.Exact
