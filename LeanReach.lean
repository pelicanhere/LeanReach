import Lean.DeclarationRange
import Lean.Meta
import Lean.PrettyPrinter.Delaborator.Builtins
import Lean.Structure
import Lean.Util.FoldConsts
import Lean.Util.Path

namespace LeanReach

open Lean Meta

private def visible (name : Name) : Bool :=
  !name.isAnonymous && !name.isInternalDetail

private abbrev Relation := NameMap NameSet

private def Relation.find (relation : Relation) (name : Name) : NameSet :=
  (relation.find? name).getD {}

private def Relation.insert (relation : Relation) (source target : Name) : Relation :=
  NameMap.insert relation source ((relation.find source).insert target)

/-- A compact name table and the reverse of Lean's direct declaration dependencies. -/
structure Index where
  private names : Array (Name × String)
  private downstream : Relation
  deriving Inhabited

private def cacheVersion := 3

private def Index.build : CoreM Index := do
  let env ← getEnv
  let mut names := #[]
  let mut downstream : Relation := {}
  for (name, info) in env.constants do
    if visible name then
      names := names.push (name, name.toString.toLower)
      for dependency in info.getUsedConstantsAsSet do
        if dependency != name && visible dependency && env.contains dependency then
          downstream := downstream.insert dependency name
  return {
    names := names.qsort fun a b => Name.lt a.1 b.1
    downstream
  }

private def moduleDepHash? (root : Name) : IO (Option String) := do
  let path := (← findOLean root).withExtension "trace"
  unless ← path.pathExists do return none
  return (Json.parse (← IO.FS.readFile path) >>= (·.getObjValAs? String "depHash")).toOption

private unsafe def Index.load (root : Name) : CoreM Index := do
  let some depHash ← moduleDepHash? root | return ← Index.build
  let path := (← findOLean root).withExtension s!"leanreach-{cacheVersion}"
  if ← path.pathExists then
    try
      let (data, _) ← readModuleData path
      let cache : String × Index := unsafe unsafeCast data
      if cache.1 == depHash then return cache.2
    catch _ =>
      pure ()
  let index ← Index.build
  try
    saveModuleData path `LeanReach.cache (unsafe unsafeCast (depHash, index))
  catch _ =>
    IO.eprintln s!"leanreach: could not write cache {path}"
  return index

structure Declaration where
  name : String
  signature : String
  moduleName : String
  file : Option String
  line : Nat
  column : Nat

instance : ToJson Declaration where
  toJson declaration := Json.mkObj [
    ("name", toJson declaration.name),
    ("signature", toJson declaration.signature),
    ("source", Json.mkObj [
      ("moduleName", toJson declaration.moduleName),
      ("file", toJson declaration.file),
      ("line", toJson declaration.line),
      ("column", toJson declaration.column)
    ])
  ]

abbrev Related := Nat × Declaration

structure QueryResult where
  target : Declaration
  upstream : Array Related
  downstream : Array Related

private def relatedJson (distance : Nat) (declaration : Declaration) : Json :=
  Json.mkObj [
    ("distance", toJson distance),
    ("declaration", toJson declaration)
  ]

instance : ToJson QueryResult where
  toJson result := Json.mkObj [
    ("target", toJson result.target),
    ("upstream", Json.arr <| result.upstream.map fun (distance, declaration) =>
      relatedJson distance declaration),
    ("downstream", Json.arr <| result.downstream.map fun (distance, declaration) =>
      relatedJson distance declaration)
  ]

structure QueryOptions where
  depth : Nat := 1
  limit : Nat := 20
  upstream : Bool := true
  downstream : Bool := true

structure Session where
  index : Index
  sourcePath : SearchPath
  private declarations : IO.Ref (NameMap Declaration)

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

private def Index.resolve (index : Index) (query : String) : CoreM Name := do
  let env ← getEnv
  let exact := query.toName
  if visible exact && env.contains exact then return exact
  let buckets := index.matchBuckets query 10
  let candidates := (buckets.find? fun bucket => !bucket.isEmpty).getD #[]
  if candidates.size == 1 then
    return candidates[0]!
  if candidates.isEmpty then
    throwError "no declaration name contains '{query}'"
  throwError "ambiguous declaration '{query}':\n{String.intercalate "\n" <|
    candidates.toList.map fun name => s!"  {name}"}"

private def renderSignature (name : Name) : MetaM String := do
  let expression ← mkConstWithLevelParams name
  let (stx, _) ← PrettyPrinter.delabCore expression
    (delab := PrettyPrinter.Delaborator.delabConstWithSignature (universes := false))
  return (← PrettyPrinter.ppTerm ⟨stx⟩).pretty (width := 10000)

private def renderList (label : String) (names : Array Name) : MetaM String := do
  if names.isEmpty then return ""
  let lines ← names.mapM renderSignature
  return s!"\n  {label}:\n    {String.intercalate "\n    " lines.toList}"

private def renderDeclaration (name : Name) (info : ConstantInfo) : MetaM String :=
    withCurrHeartbeats do
  let signature ← renderSignature name
  if ← isProp info.type then return signature
  if let some value := info.value? (allowOpaque := true) then
    let body := (← PrettyPrinter.ppExpr value).pretty (width := 100)
    return s!"{signature} :=\n  {body.replace "\n" "\n  "}"
  let .inductInfo inductiveInfo := info | return signature
  let env ← getEnv
  let fields :=
    if isStructure env name then
      getStructureFieldsFlattened env name (includeSubobjectFields := false)
        |>.filterMap (getProjFnForField? env name)
    else #[]
  return signature ++
    (← renderList "fields" fields) ++
    (← renderList "constructors" inductiveInfo.ctors.toArray)

private def describe (session : Session) (name : Name) : CoreM Declaration := do
  if let some declaration := (← session.declarations.get).find? name then
    return declaration
  let env ← getEnv
  let some info := env.find? name | throwError "unknown declaration '{name}'"
  let moduleName? ← findModuleOf? name
  let file? ← match moduleName? with
    | some moduleName =>
      pure ((← session.sourcePath.findModuleWithExt "lean" moduleName).map (·.toString))
    | none => pure none
  let range? := (← findDeclarationRanges? name).map (·.selectionRange)
  let declaration := {
    name := name.toString
    signature := ← MetaM.run' (renderDeclaration name info)
    moduleName := moduleName?.map (·.toString) |>.getD ""
    file := file?
    line := range?.map (·.pos.line) |>.getD 0
    column := range?.map (·.pos.column + 1) |>.getD 0
  }
  session.declarations.modify (·.insert name declaration)
  return declaration

private def directUpstream (name : Name) : CoreM NameSet := do
  let env ← getEnv
  let some info := env.find? name | return {}
  return info.getUsedConstantsAsSet.filter fun dependency =>
    dependency != name && visible dependency && env.contains dependency

private def traverse (start : Name) (depth limit : Nat)
    (neighbors : Name → CoreM NameSet) : CoreM (Array (Nat × Name)) := do
  if depth == 0 || limit == 0 then return #[]
  let mut visited : NameHashSet := ({} : NameHashSet).insert start
  let mut frontier := #[start]
  let mut found := #[]
  for distance in [1:depth + 1] do
    let mut next := #[]
    for name in frontier do
      for neighbor in ← neighbors name do
        unless visited.contains neighbor do
          visited := visited.insert neighbor
          next := next.push neighbor
          found := found.push (distance, neighbor)
          if found.size == limit then return found
    frontier := next
    if frontier.isEmpty then break
  return found

private def describeRelated (session : Session) (items : Array (Nat × Name)) :
    CoreM (Array Related) :=
  items.mapM fun (distance, name) => return (distance, ← describe session name)

def Session.query (session : Session) (query : String) (options : QueryOptions := {}) :
    CoreM QueryResult := do
  let target ← session.index.resolve query
  let upstream ←
    if options.upstream then
      traverse target options.depth options.limit directUpstream
    else pure #[]
  let downstream ←
    if options.downstream then
      traverse target options.depth options.limit fun name =>
        pure (session.index.downstream.find name)
    else pure #[]
  return {
    target := ← describe session target
    upstream := ← describeRelated session upstream
    downstream := ← describeRelated session downstream
  }

def Session.search (session : Session) (query : String) (limit : Nat := 20) :
    CoreM (Array Declaration) := do
  let names := session.index.search query limit
  names.mapM (describe session)

private def initializePaths : IO SearchPath := do
  match ← IO.getEnv "LEAN_PATH" with
  | some path => searchPathRef.set (System.SearchPath.parse path)
  | none => initSearchPath (← findSysroot)
  let fallback := [← IO.currentDir, (← findSysroot) / "src" / "lean"]
  match ← IO.getEnv "LEAN_SRC_PATH" with
  | some path => return System.SearchPath.parse path ++ fallback
  | none => return fallback

/--
Import one root module with all environment extensions, then reuse the environment and index for
the entire action. Run the binary through `lake env` to search another local Lake workspace.
-/
unsafe def withSession {α : Type} (root : Name) (action : Session → CoreM α) : IO α := do
  let sourcePath ← initializePaths
  let declarations ← IO.mkRef {}
  Lean.enableInitializersExecution
  let env ← importModules (loadExts := true) #[{ module := root }] {}
  Core.CoreM.toIO'
    (do action { index := ← unsafe Index.load root, sourcePath, declarations })
    { fileName := "<leanreach>", fileMap := default }
    { env }

end LeanReach
