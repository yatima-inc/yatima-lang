import Yatima.Name
import Yatima.Expr

namespace Yatima

structure Axiom where
  name : Name
  lvls : List Name
  type : ExprCid
  safe : Bool

structure AxiomAnon where
  lvls : Nat
  type : ExprAnonCid
  safe : Bool

structure AxiomMeta where
  name : Name
  lvls : List Name
  type : ExprMetaCid

structure Theorem where
  name  : Name
  lvls  : List Name
  type  : ExprCid
  value : ExprCid

structure TheoremAnon where
  lvls  : Nat
  type  : ExprAnonCid
  value : ExprAnonCid

structure TheoremMeta where
  name  : Name
  lvls  : List Name
  type  : ExprMetaCid
  value : ExprMetaCid

structure Opaque where
  name  : Name
  lvls  : List Name
  type  : ExprCid
  value : ExprCid
  safe  : Bool

structure OpaqueAnon where
  lvls  : Nat
  type  : ExprAnonCid
  value : ExprAnonCid
  safe  : Bool

structure OpaqueMeta where
  name  : Name
  lvls  : List Name
  type  : ExprMetaCid
  value : ExprMetaCid

inductive DefinitionSafety where
  | safe | «unsafe» | «partial»

structure Definition where
  name   : Name
  lvls   : List Name
  type   : ExprCid
  value  : ExprCid
  safety : DefinitionSafety

structure DefinitionAnon where
  lvls   : Nat
  type   : ExprAnonCid
  value  : ExprAnonCid
  safety : DefinitionSafety

structure DefinitionMeta where
  name  : Name
  lvls  : List Name
  type  : ExprMetaCid
  value : ExprMetaCid

structure MutualDefinitionBlock where
  defs : List $ List Definition

structure MutualDefinitionBlockAnon where
  defs : List DefinitionAnon

structure MutualDefinitionBlockMeta where
  defs : List $ List DefinitionMeta

structure MutualRef where
  name  : Name
  lvls  : List Name
  type  : ExprCid
  block : BlockCid
  index : Nat

structure MutualRefAnon where
  lvls  : Nat
  type  : ExprAnonCid
  block : BlockAnonCid
  index : Nat

structure MutualRefMeta where
  name  : Name
  lvls  : List Name
  type  : ExprMetaCid
  block : BlockMetaCid
  index : Nat

structure MutualDefinitionAnon where
  lvls  : Nat
  type  : ExprAnonCid
  block : ConstAnonCid
  index : Nat

structure ConstructorInfo where
  name   : Name
  type   : ExprCid
  params : Nat
  fields : Nat

structure ConstructorInfoAnon where
  type   : ExprAnonCid
  params : Nat
  fields : Nat

structure ConstructorInfoMeta where
  name   : Name
  type   : ExprMetaCid

structure RecursorRule where
  ctor   : Nat ⊕ ConstCid -- `Nat` for internal
  fields : Nat
  rhs    : ExprCid

structure RecursorRuleAnon where
  ctor   : Nat ⊕ ConstAnonCid -- `Nat` for internal
  fields : Nat
  rhs    : ExprAnonCid

structure RecursorRuleMeta where
  ctor   : Option ConstMetaCid -- `none` for internal
  rhs    : ExprMetaCid

structure RecursorInfo where
  name    : Name
  type    : ExprCid
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  rules   : List RecursorRule
  k       : Bool

structure RecursorInfoAnon where
  type    : ExprAnonCid
  params  : Nat
  indices : Nat
  motives : Nat
  minors  : Nat
  rules   : List RecursorRuleAnon
  k       : Bool

structure RecursorInfoMeta where
  name    : Name
  type    : ExprMetaCid
  rules   : List RecursorRuleMeta

structure Inductive where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  params  : Nat
  indices : Nat
  ctors   : List ConstructorInfo
  internalRecrs : List RecursorInfo
  externalRecrs : List RecursorInfo
  recr    : Bool
  safe    : Bool
  refl    : Bool

structure InductiveAnon where
  lvls    : Nat
  type    : ExprAnonCid
  params  : Nat
  indices : Nat
  ctors   : List ConstructorInfoAnon
  internalRecrs : List RecursorInfoAnon
  externalRecrs : List RecursorInfoAnon
  recr    : Bool
  safe    : Bool
  refl    : Bool

structure InductiveMeta where
  name    : Name
  lvls    : List Name
  type    : ExprMetaCid
  ctors   : List ConstructorInfoMeta
  internalRecrs : List RecursorInfoMeta
  externalRecrs : List RecursorInfoMeta

inductive Block
  | defBlock : List (List Definition) → Block
  | indBlock : List Inductive → Block

structure Constructor where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  block   : BlockCid
  ind     : Nat
  index   : Nat

structure ConstructorAnon where
  lvls    : Nat
  type    : ExprAnonCid
  block   : BlockAnonCid
  ind     : Nat
  index   : Nat

structure ConstructorMeta where
  name    : Name
  lvls    : List Name
  type    : ExprMetaCid
  block   : BlockMetaCid

structure Recursor where
  name    : Name
  lvls    : List Name
  type    : ExprCid
  block   : BlockCid
  ind     : Nat
  index   : Nat
  intern  : Bool

structure RecursorAnon where
  lvls    : Nat
  type    : ExprAnonCid
  block   : BlockAnonCid
  ind     : Nat
  index   : Nat
  intern  : Bool

structure RecursorMeta where
  name    : Name
  lvls    : List Name
  type    : ExprMetaCid
  block   : BlockMetaCid

inductive QuotKind where
  | type | ctor | lift | ind

structure Quotient where
  name : Name
  lvls : List Name
  type : ExprCid
  kind : QuotKind

structure QuotientAnon where
  lvls : Nat
  type : ExprAnonCid
  kind : QuotKind

structure QuotientMeta where
  name : Name
  lvls : List Name
  type : ExprMetaCid

inductive Const
  | «axiom»     : Axiom → Const
  | «theorem»   : Theorem → Const
  | opaque      : Opaque → Const
  | quotient    : Quotient → Const
  | definition  : Definition → Const
  | «inductive» : Inductive → Const
  | constructor : Constructor → Const
  | recursor    : Recursor → Const
  | mutInd      : MutualRef → Const
  | mutDef      : MutualRef → Const

inductive ConstAnon
  | «axiom»     : AxiomAnon → ConstAnon
  | «theorem»   : TheoremAnon → ConstAnon
  | opaque      : OpaqueAnon → ConstAnon
  | quotient    : QuotientAnon → ConstAnon
  | definition  : DefinitionAnon → ConstAnon
  | «inductive» : InductiveAnon → ConstAnon
  | constructor : ConstructorAnon → ConstAnon
  | recursor    : RecursorAnon → ConstAnon
  | mutDef      : MutualRefAnon → ConstAnon
  | mutInd      : MutualRefAnon → ConstAnon

inductive ConstMeta
  | «axiom»     : AxiomMeta → ConstMeta
  | «theorem»   : TheoremMeta → ConstMeta
  | opaque      : OpaqueMeta → ConstMeta
  | quotient    : QuotientMeta → ConstMeta
  | definition  : DefinitionMeta → ConstMeta
  | «inductive» : InductiveMeta → ConstMeta
  | constructor : ConstructorMeta → ConstMeta
  | recursor    : RecursorMeta → ConstMeta
  | mutDef      : MutualRefMeta → ConstMeta
  | mutInd      : MutualRefMeta → ConstMeta

def Definition.toAnon (d : Definition) : DefinitionAnon :=
  ⟨d.lvls.length, d.type.anon, d.value.anon, d.safety⟩

def MutualRef.toAnon (d : MutualRef) : MutualRefAnon :=
  ⟨d.lvls.length, d.type.anon, d.block.anon, d.index⟩

def ConstructorInfo.toAnon (x : ConstructorInfo) : ConstructorInfoAnon :=
  ⟨x.type.anon, x.params, x.fields⟩

def RecursorRule.toAnon (x : RecursorRule) : RecursorRuleAnon :=
  match x.ctor with
  | .inl i => ⟨.inl i, x.fields, x.rhs.anon⟩
  | .inr y => ⟨.inr y.anon, x.fields, x.rhs.anon⟩

def RecursorInfo.toAnon (x: RecursorInfo) : RecursorInfoAnon :=
  ⟨ x.type.anon
  , x.params
  , x.indices
  , x.motives
  , x.minors
  , x.rules.map RecursorRule.toAnon
  , x.k ⟩

def Inductive.toAnon (x: Inductive) : InductiveAnon :=
  ⟨ x.lvls.length
  , x.type.anon
  , x.params
  , x.indices
  , x.ctors.map (·.toAnon)
  , x.internalRecrs.map RecursorInfo.toAnon
  , x.externalRecrs.map RecursorInfo.toAnon
  , x.recr
  , x.safe
  , x.refl ⟩

def Const.toAnon : Const → ConstAnon
  | .axiom a => .axiom ⟨a.lvls.length, a.type.anon, a.safe⟩
  | .theorem t => .theorem ⟨t.lvls.length, t.type.anon, t.value.anon⟩
  | .opaque o => .opaque ⟨o.lvls.length, o.type.anon, o.value.anon, o.safe⟩
  | .quotient q => .quotient ⟨q.lvls.length, q.type.anon, q.kind⟩
  | .definition d => .definition d.toAnon
  | .inductive i => .inductive ⟨i.lvls.length, i.type.anon, i.params, i.indices, 
      i.ctors.map (·.toAnon), i.internalRecrs.map (·.toAnon), i.externalRecrs.map (·.toAnon), i.recr, i.safe, i.refl⟩
  | .constructor c => .constructor 
    ⟨ c.lvls.length
    , c.type.anon
    , c.block.anon
    , c.ind
    , c.index ⟩
  | .recursor r => .recursor
    ⟨ r.lvls.length
    , r.type.anon
    , r.block.anon
    , r.ind
    , r.index
    , r.intern ⟩
  | .mutDef x => .mutDef x.toAnon
  | .mutInd x => .mutInd x.toAnon

def Definition.toMeta (d: Definition) : DefinitionMeta :=
  ⟨d.name, d.lvls, d.type.meta, d.value.meta⟩

def MutualRef.toMeta (d : MutualRef) : MutualRefMeta :=
  ⟨d.name, d.lvls, d.type.meta, d.block.meta, d.index⟩

def ConstructorInfo.toMeta (x: ConstructorInfo) : ConstructorInfoMeta :=
  ⟨x.name, x.type.meta⟩

def RecursorRule.toMeta (x: RecursorRule) : RecursorRuleMeta :=
  match x.ctor with
  | .inl _ => ⟨none, x.rhs.meta⟩
  | .inr y => ⟨some y.meta, x.rhs.meta⟩

def RecursorInfo.toMeta (x: RecursorInfo) : RecursorInfoMeta :=
  ⟨x.name, x.type.meta, x.rules.map RecursorRule.toMeta⟩

def Inductive.toMeta (x: Inductive) : InductiveMeta :=
  ⟨ x.name
  , x.lvls
  , x.type.meta
  , x.ctors.map (·.toMeta)
  , x.internalRecrs.map RecursorInfo.toMeta
  , x.externalRecrs.map RecursorInfo.toMeta ⟩

def Const.toMeta : Const → ConstMeta
  | .axiom a => .axiom ⟨a.name, a.lvls, a.type.meta⟩
  | .theorem t => .theorem ⟨t.name, t.lvls, t.type.meta, t.value.meta⟩
  | .opaque o => .opaque ⟨o.name, o.lvls, o.type.meta, o.value.meta⟩
  | .quotient q => .quotient ⟨q.name, q.lvls, q.type.meta⟩
  | .definition d => .definition d.toMeta
  | .inductive i => .inductive i.toMeta
  | .constructor c => .constructor ⟨c.name, c.lvls, c.type.meta, c.block.meta⟩
  | .recursor r => .recursor ⟨r.name, r.lvls, r.type.meta, r.block.meta⟩
  | .mutDef x => .mutDef x.toMeta
  | .mutInd x => .mutInd x.toMeta

def Const.lvlsAndType (x : Const) : (List Name) × ExprCid := by
  cases x <;> next x => exact (x.lvls, x.type)

def Const.name (x : Const) : Name := by
  cases x <;> next x => exact x.name

def Const.ctorName : Const → String
  | .axiom       _ => "axiom"
  | .theorem     _ => "theorem"
  | .opaque      _ => "opaque"
  | .quotient    _ => "quotient"
  | .definition  _ => "definition"
  | .inductive   _ => "inductive"
  | .constructor _ => "constructor"
  | .recursor    _ => "recursor"
  | .mutDef      _ => "mutDef"
  | .mutInd      _ => "mutInd"

end Yatima
