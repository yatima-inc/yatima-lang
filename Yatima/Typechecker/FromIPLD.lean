import Yatima.Store
import Yatima.Typechecker.Expr
import YatimaStdLib.RBMap

namespace Yatima.Typechecker
open Std (RBMap)

-- Conversion monad
inductive ConvError where
| cannotFindAnon : ConvError
| cannotFindMeta : ConvError
| anonMetaMismatch : ConvError
| ipldError : ConvError
| cannotStoreValue : ConvError
deriving Inhabited

structure State where
 expr_cache : RBMap ExprCid Expr compare
 const_cache : RBMap ConstCid Const compare
 univ_cache : RBMap UnivCid Univ compare

abbrev ConvM := ReaderT Store <| StateT State <| ExceptT ConvError Id
instance : Monad ConvM := let i := inferInstanceAs (Monad ConvM); { pure := i.pure, bind := i.bind }

instance (α : Type) : Inhabited (ConvM α) where
  default _ := throw .ipldError

-- Auxiliary definitions
inductive Key : Type → Type
  | univ_cache  : UnivCid      → Key Univ
  | expr_cache  : ExprCid      → Key Expr
  | const_cache : ConstCid     → Key Const
  | univ_anon   : UnivAnonCid  → Key UnivAnon
  | expr_anon   : ExprAnonCid  → Key ExprAnon
  | const_anon  : ConstAnonCid → Key ConstAnon
  | univ_meta   : UnivMetaCid  → Key UnivMeta
  | expr_meta   : ExprMetaCid  → Key ExprMeta
  | const_meta  : ConstMetaCid → Key ConstMeta

def Key.find? (key : Key A) : ConvM (Option A) := do
  match key with
  | .univ_cache  univ  => pure $ (← get).univ_cache.find? univ
  | .expr_cache  expr  => pure $ (← get).expr_cache.find? expr
  | .const_cache const => pure $ (← get).const_cache.find? const
  | .univ_anon   univ  => pure $ (← read).univ_anon.find? univ
  | .expr_anon   expr  => pure $ (← read).expr_anon.find? expr
  | .const_anon  const => pure $ (← read).const_anon.find? const
  | .univ_meta   univ  => pure $ (← read).univ_meta.find? univ
  | .expr_meta   expr  => pure $ (← read).expr_meta.find? expr
  | .const_meta  const => pure $ (← read).const_meta.find? const

def Key.find (key : Key A) : ConvM A := do
  Option.option (throw .ipldError) pure (← Key.find? key)

def Key.store (key : Key A) (a : A) : ConvM Unit := do
  match key with
  | .univ_cache  univ  => modifyGet (fun stt => (() , { stt with univ_cache  := stt.univ_cache.insert univ a }))
  | .expr_cache  expr  => modifyGet (fun stt => (() , { stt with expr_cache  := stt.expr_cache.insert expr a }))
  | .const_cache const => modifyGet (fun stt => (() , { stt with const_cache := stt.const_cache.insert const a }))
  | _ => throw .cannotStoreValue

def getInductiveAnon (const : Yatima.ConstAnon) (idx : Nat) : ConvM Yatima.InductiveAnon :=
  match const with
  | .mutIndBlock inds => pure $ inds.get! idx
  | _ => throw .ipldError

def getInductiveMeta (const : Yatima.ConstMeta) (idx : Nat) : ConvM Yatima.InductiveMeta :=
  match const with
  | .mutIndBlock inds => pure $ inds.get! idx
  | _ => throw .ipldError

-- Conversion functions
partial def univFromIpld (anonCid : UnivAnonCid) (metaCid : UnivMetaCid) : ConvM Univ := do
  let cid := .mk anonCid metaCid
  match <- Key.find? $ .univ_cache $ cid with
  | none => pure ()
  | some univ => return univ
  let anon ← Key.find $ .univ_anon  anonCid
  let meta ← Key.find $ .univ_meta metaCid
  let univ ← match (anon, meta) with
  | (.zero, .zero) => pure $ .zero
  | (.succ univAnon, .succ univMeta) => pure $ .succ (← univFromIpld univAnon univMeta)
  | (.max univAnon₁ univAnon₂, .max univMeta₁ univMeta₂) =>
    pure $ .max (← univFromIpld univAnon₁ univMeta₁) (← univFromIpld univAnon₂ univMeta₂)
  | (.imax univAnon₁ univAnon₂, .imax univMeta₁ univMeta₂) =>
    pure $ .imax (← univFromIpld univAnon₁ univMeta₁) (← univFromIpld univAnon₂ univMeta₂)
  | (.param idx, .param nam) => pure $ .var nam idx
  | _ => throw .anonMetaMismatch
  Key.store (.univ_cache cid) univ
  pure univ

partial def univsFromIpld (anonCids : List UnivAnonCid) (metaCids : List UnivMetaCid) : ConvM (List Univ) := do
  match (anonCids, metaCids) with
  | (anonCid :: anonCids, metaCid :: metaCids) =>
    pure $ (← univFromIpld anonCid metaCid) :: (← univsFromIpld anonCids metaCids)
  | ([], []) => pure []
  | _ => throw .anonMetaMismatch

def inductiveIsUnit (ind : InductiveAnon) : Bool :=
  if ind.recr || ind.indices != 0 then false
  else match ind.ctors with
  | [ctor] => ctor.fields != 0
  | _ => false

mutual
partial def exprFromIpld (anonCid : ExprAnonCid) (metaCid : ExprMetaCid) : ConvM Expr := do
  let cid := .mk anonCid metaCid
  match <- Key.find? $ .expr_cache $ cid with
  | none => pure ()
  | some expr => return expr
  let anon ← Key.find $ .expr_anon anonCid
  let meta ← Key.find $ .expr_meta metaCid
  let expr ← match (anon, meta) with
  | (.var idx, .var name) => pure $ .var anonCid name idx
  | (.sort uAnonCid, .sort uMetaCid) => pure $ .sort anonCid (← univFromIpld uAnonCid uMetaCid)
  | (.const cAnonCid uAnonCids, .const name cMetaCid uMetaCids) =>
    let const ← constFromIpld cAnonCid cMetaCid
    let univs ← univsFromIpld uAnonCids uMetaCids
    pure $ .const anonCid name const univs
  | (.app fncAnon argAnon, .app fncMeta argMeta) =>
    let fnc ← exprFromIpld fncAnon fncMeta
    let arg ← exprFromIpld argAnon argMeta
    pure $ .app anonCid fnc arg
  | (.lam domAnon bodAnon, .lam name binfo domMeta bodMeta) =>
    let dom ← exprFromIpld domAnon domMeta
    let bod ← exprFromIpld bodAnon bodMeta
    pure $ .lam anonCid name binfo dom bod
  | (.pi domAnon codAnon, .pi name binfo domMeta codMeta) =>
    let dom ← exprFromIpld domAnon domMeta
    let cod ← exprFromIpld codAnon codMeta
    pure $ .pi anonCid name binfo dom cod
  | (.letE typAnon valAnon bodAnon, .letE name typMeta valMeta bodMeta) =>
    let typ ← exprFromIpld typAnon typMeta
    let val ← exprFromIpld valAnon valMeta
    let bod ← exprFromIpld bodAnon bodMeta
    pure $ .letE anonCid name typ val bod
  | (.lit lit, .lit) => pure $ .lit anonCid lit
  | (.lty lty, .lty) => pure $ .lty anonCid lty
  | (.fix bodAnon, .fix name bodMeta) =>
    let bod ← exprFromIpld bodAnon bodMeta
    pure $ .fix anonCid name bod
  | (.proj idx bodAnon, .proj _ bodMeta) =>
    let bod ← exprFromIpld bodAnon bodMeta
    pure $ .proj anonCid idx bod
  | _ => throw .anonMetaMismatch
  Key.store (.expr_cache cid) expr
  pure expr

partial def constFromIpld (anonCid : ConstAnonCid) (metaCid : ConstMetaCid) : ConvM Const := do
  let cid := .mk anonCid metaCid
  match <- Key.find? $ .const_cache $ cid with
  | none => pure ()
  | some const => return const
  let anon ← Key.find $ .const_anon anonCid
  let meta ← Key.find $ .const_meta metaCid
  let const ← match (anon, meta) with
  | (.«axiom» axiomAnon, .«axiom» axiomMeta) =>
    let name := axiomMeta.name
    let lvls := axiomMeta.lvls
    let type ← exprFromIpld axiomAnon.type axiomMeta.type
    let safe := axiomAnon.safe
    pure $ .«axiom» anonCid { name, lvls, type, safe }
  | (.«theorem» theoremAnon, .«theorem» theoremMeta) =>
    let name := theoremMeta.name
    let lvls := theoremMeta.lvls
    let type ← exprFromIpld theoremAnon.type theoremMeta.type
    let value ← exprFromIpld theoremAnon.value theoremMeta.value
    pure $ .«theorem» anonCid { name, lvls, type, value }
  | (.inductiveProj anon, .inductiveProj meta) =>
    let inductiveAnon ← getInductiveAnon (← Key.find $ .const_anon anon.block) anon.idx
    let inductiveMeta ← getInductiveMeta (← Key.find $ .const_meta meta.block) anon.idx
    let name := inductiveMeta.name
    let lvls := inductiveMeta.lvls
    let type ← exprFromIpld inductiveAnon.type inductiveMeta.type
    let params := inductiveAnon.params
    let indices := inductiveAnon.indices
    let ctors ← ctorsFromIpld inductiveAnon.ctors inductiveMeta.ctors
    let recr := inductiveAnon.recr
    let safe := inductiveAnon.safe
    let refl := inductiveAnon.refl
    let unit := inductiveIsUnit inductiveAnon
    pure $ .«inductive» anonCid { name, lvls, type, params, indices, ctors, recr, safe, refl, unit }
  | (.opaque opaqueAnon, .opaque opaqueMeta) =>
    let name := opaqueMeta.name
    let lvls := opaqueMeta.lvls
    let type ← exprFromIpld opaqueAnon.type opaqueMeta.type
    let value ← exprFromIpld opaqueAnon.value opaqueMeta.value
    let safe := opaqueAnon.safe
    pure $ .opaque anonCid { name, lvls, type, value, safe }
  | (.definition definitionAnon, .definition definitionMeta) =>
    let name := definitionMeta.name
    let lvls := definitionMeta.lvls
    let type ← exprFromIpld definitionAnon.type definitionMeta.type
    let value ← exprFromIpld definitionAnon.value definitionMeta.value
    let safety := definitionAnon.safety
    pure $ .definition anonCid { name, lvls, type, value, safety }
  | (.constructorProj anon, .constructorProj meta) =>
    let inductiveAnon ← getInductiveAnon (← Key.find $ .const_anon anon.block) anon.idx
    let inductiveMeta ← getInductiveMeta (← Key.find $ .const_meta meta.block) anon.idx
    let constructorAnon ← Option.option (throw .ipldError) pure (inductiveAnon.ctors.get? anon.cidx);
    let constructorMeta ← Option.option (throw .ipldError) pure (inductiveMeta.ctors.get? anon.cidx);
    let name := constructorMeta.name
    let type ← exprFromIpld constructorAnon.type constructorMeta.type
    let params := constructorAnon.params
    let fields := constructorAnon.fields
    let rhs ← exprFromIpld constructorAnon.rhs constructorMeta.rhs
    pure $ .constructor anonCid { name, type, params, fields, rhs }
  | (.recursorProj anon, .recursorProj meta) =>
    let inductiveAnon ← getInductiveAnon (← Key.find $ .const_anon anon.block) anon.idx
    let inductiveMeta ← getInductiveMeta (← Key.find $ .const_meta meta.block) anon.idx
    let pairAnon ← Option.option (throw .ipldError) pure (inductiveAnon.recrs.get? anon.ridx);
    let pairMeta ← Option.option (throw .ipldError) pure (inductiveMeta.recrs.get? anon.ridx);
    let recursorAnon := Sigma.snd pairAnon
    let recursorMeta := Sigma.snd pairMeta
    let name := recursorMeta.name
    let lvls := recursorMeta.lvls
    let type ← exprFromIpld recursorAnon.type recursorMeta.type
    let params := recursorAnon.params
    let indices := recursorAnon.indices
    let motives := recursorAnon.motives
    let minors := recursorAnon.minors
    let k := recursorAnon.k
    let b₁ := Sigma.fst pairAnon
    let b₂ := Sigma.fst pairMeta
    let casesExtInt := Bool.casesOn (motive := fun b₁ => (RecursorAnon b₁) → (RecursorMeta b₂) → ConvM Const) b₁
      -- Case where recursorAnon is external
      (fun recursorAnon => Bool.casesOn b₂ (motive := fun b₂ => (RecursorMeta b₂) → ConvM Const)
        -- Case where recursorMeta is also external
        (fun recursorMeta => do
             let rules ← rulesFromIpld recursorAnon.rules recursorMeta.rules
             pure $ .extRecursor anonCid { name, lvls, type, params, indices, motives, minors, rules, k })
        (fun _ => throw .ipldError))
      -- Case where recursorAnon is internal
      (fun _ => Bool.casesOn b₂ (motive := fun b₂ => (RecursorMeta b₂) → ConvM Const)
        (fun _ => throw .ipldError)
        -- Case where recursorMeta is also internal
        (fun _ => pure $ .intRecursor anonCid { name, lvls, type, params, indices, motives, minors, k }))
    casesExtInt recursorAnon recursorMeta
  | (.quotient quotientAnon, .quotient quotientMeta) =>
    let name := quotientMeta.name
    let lvls := quotientMeta.lvls
    let type ← exprFromIpld quotientAnon.type quotientMeta.type
    let kind := quotientAnon.kind
    pure $ .quotient anonCid { name, lvls, type, kind }
  | _ => throw .anonMetaMismatch
  Key.store (.const_cache cid) const
  pure const

partial def ctorsFromIpld (ctorsAnon : List ConstructorAnon) (ctorsMeta : List ConstructorMeta) : ConvM (List (Constructor Expr)) :=
  match (ctorsAnon, ctorsMeta) with
  | (ctorAnon :: ctorsAnon, ctorMeta :: ctorsMeta) => do
    let ctor ← ctorFromIpld ctorAnon ctorMeta
    let ctors ← ctorsFromIpld ctorsAnon ctorsMeta
    pure $ ctor :: ctors
  | ([], []) => pure []
  | _ => throw .anonMetaMismatch

partial def ctorFromIpld (ctorAnon : ConstructorAnon) (ctorMeta : ConstructorMeta) : ConvM (Constructor Expr) := do
  let type ← exprFromIpld ctorAnon.type ctorMeta.type
  let rhs ← exprFromIpld ctorAnon.rhs ctorMeta.rhs
  pure { name := ctorMeta.name, type, params := ctorAnon.params, fields := ctorAnon.fields, rhs }

partial def rulesFromIpld (rulesAnon : List RecursorRuleAnon) (rulesMeta : List RecursorRuleMeta) : ConvM (List (RecursorRule Expr)) :=
  match (rulesAnon, rulesMeta) with
  | (ruleAnon :: rulesAnon, ruleMeta :: rulesMeta) => do
    let rhs ← exprFromIpld ruleAnon.rhs ruleMeta.rhs
    let rules ← rulesFromIpld rulesAnon rulesMeta
    pure $ { rhs, ctor := ruleAnon.ctor, fields := ruleAnon.fields } :: rules
  | ([], []) => pure []
  | _ => throw .anonMetaMismatch
end

end Yatima.Typechecker
