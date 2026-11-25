module

public import Silmaril.Semantics.RuntimeWires.Sliced.Defs

@[expose] public section

/-!
# Composition and tensor of progressive slices

Algebraic comparison for Lemma 3.4 and Theorem 3.6 (pp. 9:7–9:8) of Mario
Román and Paweł Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

namespace Row

/-- Relabel an equal frontier without changing any cell. -/
def reindex {A B C D : List O} (hA : A = C) (hB : B = D) (r : Row S A B) : Row S C D :=
  hA ▸ hB ▸ r

/-- Place two rows side by side in their given order. -/
def beside {A B X Y : List O} (p : Row S A B) (q : Row S X Y) :
    Row S (A ++ X) (B ++ Y) :=
  match p with
  | .empty => q
  | .wire x r => .wire x (beside r q)
  | .box e r => reindex (List.append_assoc ..).symm (List.append_assoc ..).symm
      (.box e (beside r q))

end Row

namespace Sheet

/-- Relabel equal frontiers without changing any row. -/
def reindex {A B C D : List O} (hA : A = C) (hB : B = D) (p : Sheet S A B) : Sheet S C D :=
  hA ▸ hB ▸ p

/-- Glue the last frontier of one sheet to the first frontier of the next. -/
def thenDo {A B C : List O} (p : Sheet S A B) (q : Sheet S B C) : Sheet S A C :=
  match p with
  | .empty _ => q
  | .cons r p => .cons r (thenDo p q)

/-- Carry through wires to the left of a sheet. -/
def padLeft (W : List O) {A B : List O} (p : Sheet S A B) : Sheet S (W ++ A) (W ++ B) :=
  match p with
  | .empty A => .empty (W ++ A)
  | .cons r p => .cons (Row.pass W r) (padLeft W p)

/-- Carry through wires to the right of a sheet. -/
def padRight {A B : List O} (p : Sheet S A B) (W : List O) : Sheet S (A ++ W) (B ++ W) :=
  match p with
  | .empty A => .empty (A ++ W)
  | .cons r p => .cons (r.beside (Row.straight W)) (padRight p W)

/-- Tensor two sheets by scheduling the left one before the right one. -/
def tensor {A B X Y : List O} (p : Sheet S A B) (q : Sheet S X Y) :
    Sheet S (A ++ X) (B ++ Y) :=
  (p.padRight X).thenDo (q.padLeft B)

/-- A single generating box. -/
def generator (e : S.Edge) : Sheet S (S.source e) (S.target e) :=
  reindex (List.append_nil _) (List.append_nil _) (.cons (.box e .empty) (.empty _))

end Sheet

end Silmaril.RuntimeWires.Sliced
