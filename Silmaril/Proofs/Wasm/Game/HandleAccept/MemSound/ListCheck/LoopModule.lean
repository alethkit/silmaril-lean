module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopSound
import Silmaril.Wasm.Execution.Core.Soundness.PureRedex

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopSound

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.Game.IOAccept Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Items
  Silmaril.Wasm.Game.HandleAccept.MemSound.Readers Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck
  Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Game.HandleAccept.Memory (MemAtom)

open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound in
def shapeOk (ix : ListImports) (pages : InitialPages := InitialPages.one) : Bool :=
  ix.child != ix.items &&
  match prep (Loop.mod ix pages) with
  | some (cfg, start) => start.isNone && cfg.code.isEmpty && cfg.frame.module.mems == [0] &&
      exportFuncAddrs cfg.frame.module == [3] && cfg.store.mems.length == 1 &&
      (match cfg.store.funcs with
       | [items, child, accept, check] => stubOk 0 2 items && stubOk 1 2 child && stubOk 2 1 accept &&
          check.type.expand? == some (Ty.funcOf [.i32] []) &&
          fnOk [.i32, .i32, .i32] body 1 0 [0, 1, 2, 3] [0]
            [some (.i32 0), some (.i32 0), some (.i32 0)] check
       | _ => false)
  | none => false

theorem sym_shape : shapeOk {} = true := by decide +kernel

theorem blob_shape : shapeOk blobImports = true := by decide +kernel

open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
open Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers (X.loop)
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck
  (ChildKind listReaderLang_subset symTextAns_kind blobAns_kind)

def StoreInv (ix : ListImports) (pages : InitialPages) (store : Store Nat) : Prop :=
  ∃ cfg start, prep (Loop.mod ix pages) = some (cfg, start) ∧
    store.funcs = cfg.store.funcs ∧ store.mems.length = 1

theorem shape_facts {ix : ListImports} {pages : InitialPages} (valid : shapeOk ix pages = true)
    {cfg : Config Nat} {start : Option FuncIdx} (prepared : prep (Loop.mod ix pages) = some (cfg, start)) :
    ix.child ≠ ix.items ∧ start = none ∧ cfg.code = [] ∧ cfg.frame.module.mems = [0] ∧
    exportFuncAddrs cfg.frame.module = [3] ∧ cfg.store.mems.length = 1 ∧
    ∃ items child accept check, cfg.store.funcs = [items, child, accept, check] ∧
      stubOk 0 2 items = true ∧ stubOk 1 2 child = true ∧ stubOk 2 1 accept = true ∧
      check.type.expand? = some (Ty.funcOf [.i32] []) ∧
      fnOk [.i32, .i32, .i32] body 1 0 [0, 1, 2, 3] [0]
        [some (.i32 0), some (.i32 0), some (.i32 0)] check = true := by
  unfold shapeOk at valid
  rw [prepared] at valid
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Option.isNone_iff_eq_none,
    List.isEmpty_iff] at valid
  obtain ⟨distinct, ⟨⟨⟨⟨⟨noStart, noCode⟩, memory⟩, exports⟩, count⟩, funcs⟩⟩ := valid
  refine ⟨distinct, noStart, noCode, memory, exports, count, ?_⟩
  split at funcs
  · rename_i items child accept check found
    simp only [Bool.and_eq_true, beq_iff_eq] at funcs
    obtain ⟨⟨⟨⟨okItems, okChild⟩, okAccept⟩, type⟩, okCheck⟩ := funcs
    exact ⟨items, child, accept, check, found, okItems, okChild, okAccept, type, okCheck⟩
  · cases funcs

theorem sat (profile : Profile) {ix : ListImports} {pages : InitialPages} (valid : shapeOk ix pages = true)
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)} {kind : Set SymStrBytesSExp}
    (childKind : ChildKind ans kind) (env : Env (BitVec 32) SymStrBytesSExp) :
    MemSat profile (Loop.mod ix pages) 0 (listRoles ix ans) (Contract ix kind env) (StoreInv ix pages) := by
  intro mt imports config spec
  obtain ⟨cfg, start, prepared, rfl, _, exported⟩ := prep_of_spec spec
  obtain ⟨distinct, rfl, noCode, mems, exports, hasMemory, items, child, accept, check,
    storeFuncs, okItems, okChild, okAccept, declared, okCheck⟩ := shape_facts valid prepared
  have memoryAddr : (cfg.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, mems]
  rw [memoryAddr]
  refine ⟨fun _ => Safe.of_exits (o := .normal []) (by simp [Config.withStart, noCode]; rfl)
    (fun _ _ => ⟨cfg, none, prepared, rfl, hasMemory⟩), ?_⟩
  intro addr member
  rw [← exported, exports] at member
  obtain rfl : addr = 3 := by simpa using member
  obtain ⟨code, params, results, hasCode, locals, hasBody, expanded, _, noResults, funcs, memory,
    defaultLocals⟩ := fnOk_spec okCheck
  have stable : ∀ st, StoreInv ix pages st → st.funcs = cfg.store.funcs := by
    rintro st ⟨cfg', start', inst, same, _⟩
    have eqCfg := (Prod.mk.inj (Option.some.inj (inst.symm.trans prepared))).1
    exact same.trans (congrArg (fun cfg : Config Nat => cfg.store.funcs) eqCfg)
  have atCheck : ∀ st, StoreInv ix pages st → st.funcs[3]? = some check := fun st inv => by
    rw [stable st inv, storeFuncs]; rfl
  refine export_valid atCheck hasCode expanded noResults ?_
  intro store args inv typed Q exits
  obtain ⟨callee, ps, rs, lookup, type, argTypes⟩ := typed
  have sameCallee : callee = check := Option.some.inj (lookup.symm.trans (atCheck store inv))
  subst callee
  have signature := Expand.iff.1 type
  rw [declared] at signature
  change some (Ty.func (Ty.ofList [.i32]) .nil) = some (Ty.func ps rs) at signature
  obtain ⟨rfl, rfl⟩ := Ty.func.inj (Option.some.inj signature)
  rcases argTypes with _ | ⟨argType, rest⟩
  cases rest
  obtain ⟨root, rfl⟩ := ValOk.num_inv argType
  have storeMemory : store.mems.length = 1 := by obtain ⟨_, _, _, _, count⟩ := inv; exact count
  have frameEq : Frame.forCall check.module [.i32 root] code.locals =
      ⟨[some (.i32 root), some (.i32 0), some (.i32 0), some (.i32 0)], check.module⟩ := by
    unfold Frame.forCall
    rw [locals, defaultLocals]
    rfl
  rw [hasBody]
  refine X.loop (Inv := Inv kind env root check.module cfg.store.funcs)
    (fun st frame invariant => round childKind distinct funcs memory
      (by rw [storeFuncs]; rfl) (by rw [storeFuncs]; rfl) (by rw [storeFuncs]; rfl)
      okItems okChild okAccept invariant (fun st same count f => (exits st
        ⟨cfg, none, prepared, same, count⟩ f).2)) ?_
  exact ⟨stable store inv, storeMemory, 0, 0, 0, frameEq, by decide,
    fun children denotes => ⟨denotes, Nat.zero_le _, fun _ _ before => by simp at before⟩⟩

theorem symbols_bounded (profile : Profile) {policy : OnInvalid} (noUB : policy ≠ .ub)
    (envs : Set (Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang profile (ReplyEnvs itemsReply) 0 (Loop.mod {}) {} symTextAns .trap policy envs ⊆
      boundedListsOf symbols :=
  listReaderLang_subset (fun env => sat profile sym_shape symTextAns_kind env) (fun _ _ h => h) noUB envs

theorem blobs_bounded (profile : Profile) {policy : OnInvalid} (noUB : policy ≠ .ub)
    (envs : Set (Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang profile (ReplyEnvs itemsReply) 0 (Loop.mod blobImports) blobImports blobAns
      .trap policy envs ⊆ boundedListsOf blobs :=
  listReaderLang_subset (fun env => sat profile blob_shape blobAns_kind env) (fun _ _ h => h) noUB envs

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopSound
