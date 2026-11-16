module

public import Silmaril.Formats.SExp.Pattern.Defs
import Silmaril.Proofs.Formats.SExp.Pattern.Basic

/-!
# Patterns, combinators and AST encodings: laws

* `mem_pair`; combinators preserve intersections and unions componentwise
  (`tuple_inter`, `pair_inter_left`, `pair_union_left`), because lists decompose uniquely;
  `tuple_subset_star`;
* `Pat.lang_ground`: a pattern without holes matches exactly its own tree;
  `Pat.lang_mono`: widening holes widens the language;
* `AST.encode_injective`: the standard AST-to-S-expression encoding is injective when tags and
  arguments are encoded injectively and argument vectors have a fixed length per tag
  (a counterexample without the length condition is in `Examples`). Hence images
  `AST.encode … '' L` of AST languages determine them (`AST.encode_image_injective`).
-/

@[expose] public section

namespace Silmaril.Formats

variable {α β : Type}

theorem mem_pair {L₁ L₂ : Set (SExp α)} {x : SExp α} :
    x ∈ pair L₁ L₂ ↔ ∃ a b, x = SExp.ofList [a, b] ∧ a ∈ L₁ ∧ b ∈ L₂ :=
  Silmaril.Proofs.Formats.SExp.Pattern.mem_pair

theorem tuple_inter (Ls Ms : List (Set (SExp α))) (h : Ls.length = Ms.length) :
    tuple (List.zipWith (· ∩ ·) Ls Ms) = tuple Ls ∩ tuple Ms :=
  Silmaril.Proofs.Formats.SExp.Pattern.tuple_inter Ls Ms h

theorem pair_inter_left (L L' M : Set (SExp α)) : pair (L ∩ L') M = pair L M ∩ pair L' M :=
  Silmaril.Proofs.Formats.SExp.Pattern.pair_inter_left L L' M

theorem pair_union_left (L L' M : Set (SExp α)) : pair (L ∪ L') M = pair L M ∪ pair L' M :=
  Silmaril.Proofs.Formats.SExp.Pattern.pair_union_left L L' M

theorem tuple_subset_star (L : Set (SExp α)) (Ls : List (Set (SExp α))) (h : ∀ M ∈ Ls, M ⊆ L) :
    tuple Ls ⊆ star L :=
  Silmaril.Proofs.Formats.SExp.Pattern.tuple_subset_star L Ls h

theorem Pat.lang_ground (e : SExp α) : Pat.lang (Pat.ground e) = {e} :=
  Silmaril.Proofs.Formats.SExp.Pattern.pat_lang_ground e

theorem Pat.lang_mono {f : Set (SExp α) → Set (SExp α)} (hf : ∀ L, L ⊆ f L) (p : Pat α) :
    Pat.lang p ⊆ Pat.lang (p.map (Sum.map id f)) :=
  Silmaril.Proofs.Formats.SExp.Pattern.pat_lang_mono hf p

theorem AST.encode_injective {S : AstSig} {tagEnc : S.Tag → SExp β}
    {argEnc : ∀ t, S.Arg t → List (SExp β)} (ht : Function.Injective tagEnc)
    (ha : ∀ t, Function.Injective (argEnc t)) (hl : AST.ArgLenFixed argEnc) :
    Function.Injective (AST.encode tagEnc argEnc) :=
  Silmaril.Proofs.Formats.SExp.Pattern.encode_injective ht ha hl

theorem AST.encode_image_injective {S : AstSig} {tagEnc : S.Tag → SExp β}
    {argEnc : ∀ t, S.Arg t → List (SExp β)} (ht : Function.Injective tagEnc)
    (ha : ∀ t, Function.Injective (argEnc t)) (hl : AST.ArgLenFixed argEnc) :
    Function.Injective (Set.image (AST.encode tagEnc argEnc)) :=
  Set.image_injective.2 (AST.encode_injective ht ha hl)

end Silmaril.Formats
