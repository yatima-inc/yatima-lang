import Lean 
import Yatima.Compiler.Frontend
import LSpec.SlimCheck.Testable
import YatimaStdLib.List

namespace List 

def takeListAux {α} : List α → List Nat → List (List α) × List α
| xs, [] => ([], xs)
| xs, n :: ns =>
  let ⟨xs₁, xs₂⟩ := xs.splitAt n
  let ⟨xss, rest⟩ := takeListAux xs₂ ns
  (xs₁ :: xss, rest)

def takeList {α} : List α → List Nat → List (List α) :=
  fun xs ns => (takeListAux xs ns).fst

def noDup [BEq α] : List α → Bool
  | [] => true 
  | x::xs => not (xs.contains x) ∧ noDup xs

def allEq [BEq α] : List α → Bool
  | [] => true 
  | [x] => true
  | x::xs => (xs.contains x) ∧ allEq xs

end List 

namespace SlimCheck.Gen 

/-- Given a list of examples, choose one. -/
def oneOf' [Inhabited α] (xs : List α) : Gen α := do
  let x ← choose Nat 0 $ xs.length - 1
  pure $ xs.get! x

end SlimCheck.Gen

open Std Lean SlimCheck Gen

structure MutualDefTest where 
  name : String 
  mutuals : RBMap String (List String × Nat) compare

def pprintTest (name : String) (info : List String × Nat) (pad := "  ") : String := 
  let (refs, offset) := info
  let refs := String.join (refs.map fun x => s!"{x} n + ")
  pad ++ s!"partial def {name} : Nat → Nat\n" ++ 
  pad ++ s!"| 0     => 0\n" ++ 
  pad ++ s!"| n + 1 => {refs}{offset}\n\n" 

instance : ToString MutualDefTest where 
  toString test := 
    s!"namespace {test.name}\n" ++ 
    s!"mutual\n\n" ++ 
    String.join (test.mutuals.toList.map fun (name, info) => pprintTest name info) ++ 
    s!"end\n" ++ 
    s!"end {test.name}\n"

def CHARS := "ABCDEFGHIJKLMNOPQRSTUVWXYZ".data

def randomMutual (name : String) : 
    Gen (MutualDefTest × RBMap Nat (List String) compare) := do 
  let nGroups ← choose Nat 1 (← getSize)
  let groups ← listOf (choose Nat 1 nGroups)
  dbg_trace s!"groups: {groups}"
  let n := groups.sum
  let as := List.enum $ (← permutationOf CHARS).takeList groups
  let as : RBMap Nat _ compare := 
    RBMap.ofList (as.map fun (n, xs) => (n, xs.map (·.toString)))
  dbg_trace s!"as: {as}"
  
  -- for each group, generate an ast and offset
  -- take subset of groups 
  -- pick a rep from 
  let mut offset := 1
  let mut mutuals : RBMap String _ compare := .empty
  for (i, group) in as do 
    let nRefs ← choose Nat 1 groups.length
    let perm ← permutationOf (List.range groups.length)
    let refs := perm.take nRefs
    for name in group do 
      let mut ast := []
      for j in refs do 
        match as.find? j with 
        | some ns => ast := (← oneOf' ns) :: ast 
        | none => pure ()
      mutuals := mutuals.insert name (ast, offset)
    offset := offset + 1
  
  pure ({
    name := name
    mutuals := mutuals
  }, as)

def assertMutual 
  (env : Yatima.Compiler.CompileState) 
  (name : String) (res : RBMap Nat (List String) compare) : 
    Bool := 
  let res := res.toList.map Prod.snd 
  let res : List (List (Option Cid)) := 
    res.map fun group => 
      group.map fun n => 
        let unsafe_name := env.cache.find? $ name ++ "." ++ n ++ "." ++ "_unsafe_rec"
        let name := env.cache.find? $ name ++ "." ++ n
        (unsafe_name <|> name).map fun (c, cid) => 
          cid.anon.data
  dbg_trace s!"{res}"
  let all : List Bool := res.map List.allEq
  all.and