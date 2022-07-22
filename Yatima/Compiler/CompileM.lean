import Yatima.Store
import Yatima.Compiler.Utils


namespace Yatima.Compiler

open Std (RBMap)

structure CompileState where
  store     : Ipld.Store
  defns     : Array Const
  cache     : RBMap Name (ConstCid × ConstIdx) compare
  mutDefIdx : RBMap Name Nat compare
  deriving Inhabited

def CompileState.union (s s' : CompileState) :
    Except String CompileState := Id.run do
  let mut cache := s.cache
  for (n, c') in s'.cache do
    match s.cache.find? n with
    | some c₁ =>
      if c₁.1 != c'.1 then return throw s!"Conflicting declarations for '{n}'"
    | none => cache := cache.insert n c'
  return .ok ⟨
    s.store.union s'.store,
    s.defns ++ s'.defns,
    cache,
    s'.mutDefIdx.fold (init := s.mutDefIdx) fun acc n i =>
      acc.insert n i
  ⟩

structure CompileEnv where
  constMap : Lean.ConstMap
  univCtx  : List Lean.Name
  bindCtx  : List Name
  recrCtx  : Std.RBMap Lean.Name (Nat × Nat) compare
  deriving Inhabited

abbrev CompileM := ReaderT CompileEnv $ EStateM String CompileState

def CompileM.run (env : CompileEnv) (ste : CompileState) (m : CompileM α) :
    Except String CompileState :=
  match EStateM.run (ReaderT.run m env) ste with
  | .ok _ ste  => .ok ste
  | .error e _ => .error e

def withName (name : Name) : CompileM α → CompileM α :=
  withReader $ fun e =>
    ⟨e.constMap, e.univCtx, name :: e.bindCtx, e.recrCtx⟩

def withResetCompileEnv (levels : List Lean.Name) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, levels, [], .empty⟩

def withRecrs (recrCtx : RBMap Lean.Name (Nat × Nat) compare) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, e.univCtx, e.bindCtx, recrCtx⟩

def withLevels (lvls : List Lean.Name) : CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, lvls, e.bindCtx, e.recrCtx⟩

inductive StoreEntry
  | univ_anon   : (Ipld.UnivCid .Anon) × (Ipld.Univ .Anon)   → StoreEntry
  | expr_anon   : (Ipld.ExprCid .Anon) × (Ipld.Expr .Anon)   → StoreEntry
  | const_anon  : (Ipld.ConstCid .Anon) × (Ipld.Const .Anon) → StoreEntry
  | univ_meta   : (Ipld.UnivCid .Meta) × (Ipld.Univ .Meta)   → StoreEntry
  | expr_meta   : (Ipld.ExprCid .Meta) × (Ipld.Expr .Meta)   → StoreEntry
  | const_meta  : (Ipld.ConstCid .Meta) × (Ipld.Const .Meta) → StoreEntry

instance : Coe ((Ipld.UnivCid .Anon) × (Ipld.Univ .Anon)) StoreEntry where coe := .univ_anon
instance : Coe ((Ipld.ExprCid .Anon) × (Ipld.Expr .Anon)) StoreEntry where coe := .expr_anon
instance : Coe ((Ipld.ConstCid .Anon) × (Ipld.Const .Anon)) StoreEntry where coe := .const_anon
instance : Coe ((Ipld.UnivCid .Meta) × (Ipld.Univ .Meta)) StoreEntry where coe := .univ_meta
instance : Coe ((Ipld.ExprCid .Meta) × (Ipld.Expr .Meta)) StoreEntry where coe := .expr_meta
instance : Coe ((Ipld.ConstCid .Meta) × (Ipld.Const .Meta)) StoreEntry where coe := .const_meta

def addToStore (y : StoreEntry) : CompileM Unit := do
  let stt ← get
  let store := stt.store
  match y with
  | .univ_anon   (cid, obj) => set { stt with store :=
    { store with univ_anon   := store.univ_anon.insert cid obj   } }
  | .univ_meta   (cid, obj) => set { stt with store :=
    { store with univ_meta   := store.univ_meta.insert cid obj   } }
  | .expr_anon   (cid, obj) => set { stt with store :=
    { store with expr_anon   := store.expr_anon.insert cid obj   } }
  | .expr_meta   (cid, obj) => set { stt with store :=
    { store with expr_meta   := store.expr_meta.insert cid obj   } }
  | .const_anon  (cid, obj) => set { stt with store :=
    { store with const_anon  := store.const_anon.insert cid obj  } }
  | .const_meta  (cid, obj) => set { stt with store :=
    { store with const_meta  := store.const_meta.insert cid obj  } }

def addToCache (name : Name) (c : ConstCid × ConstIdx) : CompileM Unit := do
  set { ← get with cache := (← get).cache.insert name c }

end Yatima.Compiler
