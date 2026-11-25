module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Defs

/-! Relational observations of the actual numbered linker and closure interpreter. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}

/-- Runtime globals are identified by their translation unit and local vertex. -/
abbrev GlobalId := Nat × Nat
abbrev GlobalRel := GlobalId → GlobalId → Prop

mutual

/-- Relate runtime colours with exact data, state and control observations.
Globals use the supplied identity relation and compare their initialized
values. Closures carry no separate numeric ID in this runtime. -/
inductive ValueRelated (m : Machine.{u, v, w} Op) (ids : GlobalRel) :
    {t : Ty V S} → m.Val t → m.Val t → Prop where
  | data {t : V} (value : m.Data t) : ValueRelated m ids (.data value) (.data value)
  | state {t : S} (value : m.State t) : ValueRelated m ids (.state value) (.state value)
  | control {n : Nat} (tag : Fin n) : ValueRelated m ids (.control tag) (.control tag)
  | global {t : ValueSort V S} {unitL unitR vertexL vertexR : Nat}
      {left right : m.Val (.value t)} (identity : ids (unitL, vertexL) (unitR, vertexR))
      (payload : ValueRelated m ids left right) :
      ValueRelated m ids (.global unitL vertexL left) (.global unitR vertexR right)
  | closure {params results context : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {left right : Tuple m.Val context}
      {bodyL : NestedTheta.Graph (Instruction Op) (context ++ params) [] sigsL results}
      {bodyR : NestedTheta.Graph (Instruction Op) (context ++ params) [] sigsR results}
      (captured : TupleRelated m ids left right)
      (body : NestedTheta.Graph.Isomorphic (Instruction Op) bodyL bodyR) :
      ValueRelated m ids (.closure left bodyL) (.closure right bodyR)

/-- Match the colours in their typed port order. -/
inductive TupleRelated (m : Machine.{u, v, w} Op) (ids : GlobalRel) :
    {ts ts' : Ports (Ty V S)} → Tuple m.Val ts → Tuple m.Val ts' → Prop where
  | nil : TupleRelated m ids .nil .nil
  | cons {t : Ty V S} {ts ts' : Ports (Ty V S)} {left right : m.Val t}
      {tailL : Tuple m.Val ts} {tailR : Tuple m.Val ts'}
      (head : ValueRelated m ids left right) (tail : TupleRelated m ids tailL tailR) :
      TupleRelated m ids (.cons left tailL) (.cons right tailR)

end

/-- Both computations exhaust or both return related typed tuples. -/
abbrev RunRelated (m : Machine.{u, v, w} Op) (ids : GlobalRel) {ts ts' : Ports (Ty V S)} :=
  Option.Rel (@TupleRelated _ _ _ m ids ts ts')

/-- A primitive may inspect runtime colours. This contract requires that such
observations respect the chosen relation, including global and closure identity. -/
def PrimitivesRespect (m : Machine.{u, v, w} Op) (ids : GlobalRel) : Prop :=
  ∀ {ins outs : Ports (Ty V S)} (opcode : Op ins outs) {left right : Tuple m.Val ins},
    TupleRelated m ids left right → TupleRelated m ids (m.primitive opcode left) (m.primitive opcode right)

/-- Only δ allocates a numeric identity in the nonrecursive linker. -/
def Allocates {args : Ports (Ty V S)} {past : List (Ports (Ty V S))} :
    {outs : Ports (Ty V S)} → Vertex Op args past outs → Prop
  | _, .delta _ => True
  | _, .lambda _ | _, .phi _ => False

end Silmaril.SSA.RVSDG.Interprocedural.Runtime
