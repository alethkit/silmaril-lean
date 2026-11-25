module

public import Silmaril.Courses.Cambridge.L2ToL3.Defs
public import Silmaril.Courses.Cambridge.L2.ResolvedCodec
public import Silmaril.Courses.Cambridge.L3.ResolvedCodec
public import Silmaril.Courses.Cambridge.AstCodec.SExpBytes
public import Silmaril.Courses.Cambridge.AstCodec.JsonBytes

/-! The resolved constructor grammar changes only the language envelope
and the location fields of assignment and dereference. The transcoders
accept the public L2 resolved-term format and emit canonical L3 bytes. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2ToL3

open AstCodec Silmaril.Formats
open Silmaril.Formats.Dasl.Encode (TotalCodec)

variable (address : Layout)

def locationTree (name : L2.Loc) : Tree := node "loc" [.atom (address name).repr]

def rewriteNode : List Tree → Tree
  | [.atom "assign", .atom name, rhs] => node "assign" [locationTree address name, rhs]
  | [.atom "deref", .atom name] => node "deref" [locationTree address name]
  | fields => SExp.ofList fields

/-- A bottom-up rewrite of canonical resolved constructor payloads. -/
def payload : Tree → Tree := AstCodec.fold SExp.atom (rewriteNode address)

@[simp] theorem payload_atom (value : String) :
    payload address (.atom value) = .atom value := rfl

private theorem payload_node (tag : String) (fields : List Tree) :
    payload address (node tag fields) =
      rewriteNode address (.atom tag :: fields.map (payload address)) := by
  rw [payload, node, fold_ofList]
  rfl

private theorem payload_type (T : L2.Ty) :
    payload address (L2.Codec.typeTree T) = L3.Codec.typeTree (ty T) := by
  induction T <;> simp [L2.Codec.typeTree, L3.Codec.typeTree, ty, payload_node, rewriteNode, *] <;> rfl

theorem payload_term (e : L2.Expr) :
    payload address (L2.ResolvedCodec.termTree e) = L3.ResolvedCodec.termTree (expr address e) := by
  induction e <;> simp [L2.ResolvedCodec.termTree, L3.ResolvedCodec.termTree, expr,
    payload_node, rewriteNode, locationTree, payload_type, *] <;> rfl

/-- Rewrite the canonical source payload and set the L3 resolved-term envelope. -/
def targetTree (e : L2.Expr) : Tree :=
  envelope "L3" "resolved-term" (payload address (L2.ResolvedCodec.termTree e))

theorem targetTree_eq (e : L2.Expr) :
    targetTree address e = L3.ResolvedCodec.termSExp.encode (expr address e) := by
  exact congrArg (envelope "L3" "resolved-term") (payload_term address e)

def treeCodec : Codec Tree := ⟨id, some, fun _ => rfl⟩

/-- Decode with the public L2 codec, rewrite its canonical payload, and print UTF-8. -/
def sexpBytes (input : Bytes) : Option Bytes :=
  ((SExpBytes.codec L2.ResolvedCodec.termSExp).decode? input).map
    (fun e => (SExpBytes.codec treeCodec).encode (targetTree address e))

def jsonBytes (input : Bytes) : Option Bytes :=
  ((JsonBytes.codec L2.ResolvedCodec.termSExp).decode? input).map
    (fun e => (JsonBytes.codec treeCodec).encode (targetTree address e))

theorem sexpBytes_encode (e : L2.Expr) :
    sexpBytes address ((SExpBytes.codec L2.ResolvedCodec.termSExp).encode e) =
      some ((SExpBytes.codec L3.ResolvedCodec.termSExp).encode (expr address e)) := by
  simp only [sexpBytes, SExpBytes.decode_encode, Option.map_some, targetTree_eq]
  rfl

theorem jsonBytes_encode (e : L2.Expr) :
    jsonBytes address ((JsonBytes.codec L2.ResolvedCodec.termSExp).encode e) =
      some ((JsonBytes.codec L3.ResolvedCodec.termSExp).encode (expr address e)) := by
  simp only [jsonBytes, JsonBytes.decode_encode, Option.map_some, targetTree_eq]
  rfl

theorem sexpBytes_canonical_injective :
    Function.Injective (fun e =>
      sexpBytes address ((SExpBytes.codec L2.ResolvedCodec.termSExp).encode e)) := by
  intro a b equal
  dsimp only at equal
  rw [sexpBytes_encode, sexpBytes_encode] at equal
  exact expr_injective address
    (SExpBytes.encode_injective L3.ResolvedCodec.termSExp (Option.some.inj equal))

theorem jsonBytes_canonical_injective :
    Function.Injective (fun e =>
      jsonBytes address ((JsonBytes.codec L2.ResolvedCodec.termSExp).encode e)) := by
  intro a b equal
  dsimp only at equal
  rw [jsonBytes_encode, jsonBytes_encode] at equal
  exact expr_injective address
    (JsonBytes.encode_injective L3.ResolvedCodec.termSExp (Option.some.inj equal))

end Silmaril.Courses.Cambridge.L2ToL3
