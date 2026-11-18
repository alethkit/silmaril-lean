module

public import Silmaril.Wasm.Region.ByteMap.Defs

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.Proofs
open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

 theorem parseAll_sound {α : Type} {G : Bytes → α → Prop} {parser : Decode.DecodeM α}
    (sound : Decode.Sound G parser) {bytes : Bytes} {a : α}
    (h : parseAll? parser bytes = some a) : G bytes a := by
  unfold parseAll? at h
  split at h
  · contradiction
  · rename_i result cursor run
    split at h
    · rename_i rest
      cases h
      obtain ⟨_, pre, hr, hg⟩ := sound run
      have eq : bytes = pre := by simpa [Decode.Cursor.rest, rest] using hr
      simpa only [← eq] using hg
    · contradiction

 theorem readOne_sound (fuel : Nat) : Decode.Sound (Binary.Core.Instr Forms.all) (readOne fuel) := by
  intro c i c' h
  obtain ⟨op, cm, hop, hi⟩ := Decode.bindOk h
  obtain ⟨hb, pre, hr, hg⟩ := (Decode.readInstr_readSeq_sound fuel).1 op hi
  obtain ⟨hb₀, pre₀, hr₀, hg₀⟩ := Decode.readByte_sound hop
  cases hg₀
  exact ⟨hb.trans hb₀, [op] ++ pre, by simp [hr₀, hr, List.append_assoc], hg⟩

 theorem span_sound {input : Input} {m : ByteMapEntry} (h : input.SpanChecks m) :
    input.DecodesAt m.decoded m.bytes := by
  obtain ⟨hf, hp, start, _, _, prefix, existsI, instr⟩ := h
  have prefix := parseAll_sound Decode.readExpr_sound prefix
  have prefix' : Instrs Forms.all (input.prefixBytes m.bytes)
      (input.body.take m.decoded.instructionOffset) := by
    cases prefix with
    | @mk b is hb =>
      have eq : b = input.prefixBytes m.bytes := List.append_cancel_right (by assumption)
      simpa [eq] using hb
  cases hi : input.body[m.decoded.instructionOffset]? with
  | none => simp [hi] at existsI
  | some i =>
    exact ⟨hf, hp, start, prefix', i, hi,
      parseAll_sound (readOne_sound _) (by simpa [hi] using instr)⟩

 def certify (input : Input) (entries : List ByteMapEntry)
    (body : input.BodyChecks) (table : input.TableChecks entries) : Certified input := by
  obtain ⟨_, size, locals, expr⟩ := body
  have hl₀ := parseAll_sound (Decode.readVec_sound Decode.readLocals_sound) locals
  have hl := Decode.vec_map expandLocal (fun _ _ h => h) hl₀
  have he := parseAll_sound Decode.readExpr_sound expr
  refine ⟨hl, he, ?_, ⟨entries, ?_, ?_, table.2.1, table.2.2⟩⟩
  · simpa only [List.take_append_drop] using Func.mk hl he size
  · exact fun m hm => span_sound (table.1 m hm)
  · intro m hm
    exact ⟨(table.1 m hm).2.2.2.1, (table.1 m hm).2.2.2.2.1⟩

end Silmaril.Wasm.Region.ByteMap.Proofs
