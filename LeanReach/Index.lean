import Lean.Meta
import Lean.Util.FoldConsts
import Lean.Util.Path

namespace LeanReach

open Lean

private def visible (name : Name) : Bool :=
  !name.isAnonymous && !name.isInternalDetail

/-- Names available for search and the reverse declaration dependency relation. -/
structure Index where
  private names : Array (Name × String)
  private reverse : NameMap NameSet
  deriving Inhabited

private def cacheVersion := 3

private def usedConstants (env : Environment) (name : Name) (info : ConstantInfo) : NameSet :=
  info.getUsedConstantsAsSet.filter fun dependency =>
    dependency != name && visible dependency && env.contains dependency

private def Index.build : CoreM Index := do
  let env ← getEnv
  let mut names := #[]
  let mut reverse : NameMap NameSet := {}
  for (name, info) in env.constants do
    if visible name then
      names := names.push (name, name.toString.toLower)
      for dependency in usedConstants env name info do
        reverse := NameMap.insert reverse dependency ((reverse.getD dependency {}).insert name)
  return {
    names := names.qsort fun a b => Name.lt a.1 b.1
    reverse
  }

private def moduleDepHash? (root : Name) : IO (Option String) := do
  let path := (← findOLean root).withExtension "trace"
  unless ← path.pathExists do return none
  return (Json.parse (← IO.FS.readFile path) >>= (·.getObjValAs? String "depHash")).toOption

unsafe def Index.load (root : Name) : CoreM Index := do
  let some depHash ← moduleDepHash? root | return ← Index.build
  let path := (← findOLean root).withExtension s!"leanreach-{cacheVersion}"
  if ← path.pathExists then
    try
      let (data, _) ← readModuleData path
      let cache : String × Index := unsafe unsafeCast data
      if cache.1 == depHash then return cache.2
    catch _ => pure ()
  let index ← Index.build
  try
    saveModuleData path `LeanReach.cache (unsafe unsafeCast (depHash, index))
  catch _ =>
    IO.eprintln s!"leanreach: could not write cache {path}"
  return index

private def Index.matchBuckets (index : Index) (query : String) (limit : Nat) :
    Array (Array Name) := Id.run do
  let query := query.toLower
  let suffix := "." ++ query
  let mut buckets : Array (Array Name) := #[#[], #[], #[]]
  for (name, lower) in index.names do
    let score? :=
      if lower == query then some 0
      else if lower.endsWith suffix then some 1
      else if lower.contains query then some 2
      else none
    if let some score := score? then
      if buckets[score]!.size < limit then
        buckets := buckets.modify score (·.push name)
  return buckets

def Index.search (index : Index) (query : String) (limit : Nat := 20) : Array Name :=
  (index.matchBuckets query limit).flatten.take limit

def Index.resolve (index : Index) (query : String) : CoreM Name := do
  let env ← getEnv
  let exact := query.toName
  if visible exact && env.contains exact then return exact
  let candidates := (index.matchBuckets query 10).find? (not ∘ Array.isEmpty) |>.getD #[]
  if candidates.size == 1 then return candidates[0]!
  if candidates.isEmpty then throwError "no declaration name contains '{query}'"
  throwError "ambiguous declaration '{query}':\n{String.intercalate "\n" <|
    candidates.toList.map fun name => s!"  {name}"}"

def Index.downstream (index : Index) (name : Name) : NameSet :=
  index.reverse.getD name {}

def directUpstream (name : Name) : CoreM NameSet := do
  let env ← getEnv
  return (env.find? name).map (usedConstants env name) |>.getD {}

end LeanReach
