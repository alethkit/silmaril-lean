module

public import Silmaril.Elf.Staged.Corpus.Cjson.X8664.LibcjsonSo1.Thms

/-! Exact canonical x86-64 cJSON predicate placements. Byte-location checks do
not establish source-to-machine semantics or full-TU frontend adequacy. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonTypePredicates
def nullAddress : Nat := 21600
def nullCode : List (BitVec 8) := [0x48, 0x85, 0xff, 0x74, 0xb, 0x31, 0xc0, 0x80, 0x7f, 0x18, 0x4, 0xf, 0x94, 0xc0, 0xc3, 0x90, 0x31, 0xc0, 0xc3]
def boolAddress : Nat := 21568
def boolCode : List (BitVec 8) := [0x48, 0x85, 0xff, 0x74, 0xb, 0x31, 0xc0, 0xf6, 0x47, 0x18, 0x3, 0xf, 0x95, 0xc0, 0xc3, 0x90, 0x31, 0xc0, 0xc3]
def numberAddress : Nat := 21632
def numberCode : List (BitVec 8) := [0x48, 0x85, 0xff, 0x74, 0xb, 0x31, 0xc0, 0x80, 0x7f, 0x18, 0x8, 0xf, 0x94, 0xc0, 0xc3, 0x90, 0x31, 0xc0, 0xc3]
def stringAddress : Nat := 21712
def stringCode : List (BitVec 8) := [0x48, 0x85, 0xff, 0x74, 0xb, 0x31, 0xc0, 0x80, 0x7f, 0x18, 0x10, 0xf, 0x94, 0xc0, 0xc3, 0x90, 0x31, 0xc0, 0xc3]
def arrayAddress : Nat := 21776
def arrayCode : List (BitVec 8) := [0x48, 0x85, 0xff, 0x74, 0xb, 0x31, 0xc0, 0x80, 0x7f, 0x18, 0x20, 0xf, 0x94, 0xc0, 0xc3, 0x90, 0x31, 0xc0, 0xc3]
def objectAddress : Nat := 21808
def objectCode : List (BitVec 8) := [0x48, 0x85, 0xff, 0x74, 0xb, 0x31, 0xc0, 0x80, 0x7f, 0x18, 0x40, 0xf, 0x94, 0xc0, 0xc3, 0x90, 0x31, 0xc0, 0xc3]
/-- The six actual exported predicates covered by this source closure. -/
inductive Predicate where
  | isNull | isBool | isNumber | isString | isArray | isObject
  deriving DecidableEq, Repr

def Predicate.name : Predicate → String
  | .isNull => "cJSON_IsNull"
  | .isBool => "cJSON_IsBool"
  | .isNumber => "cJSON_IsNumber"
  | .isString => "cJSON_IsString"
  | .isArray => "cJSON_IsArray"
  | .isObject => "cJSON_IsObject"

def Predicate.address : Predicate → Nat
  | .isNull => nullAddress
  | .isBool => boolAddress
  | .isNumber => numberAddress
  | .isString => stringAddress
  | .isArray => arrayAddress
  | .isObject => objectAddress

def Predicate.code : Predicate → List (BitVec 8)
  | .isNull => nullCode
  | .isBool => boolCode
  | .isNumber => numberCode
  | .isString => stringCode
  | .isArray => arrayCode
  | .isObject => objectCode

end Silmaril.Elf.Corpus.CjsonTypePredicates
