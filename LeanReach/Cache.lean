import Lake.Build.Trace
import Lean.Environment
import Lean.Server.References
import Lean.Util.Path
import LeanReach.BlackListed
import LeanReach.Declaration
import LeanReach.Index

namespace LeanReach.Cache

open Lean

private def catalogVersion := 5
private def relationsVersion := 5
private def fragmentVersion := 5
private def ppVersion := 3

structure ModuleFragment where
  imports : Array Name
  declarations : Array (Name × NameSet)

/-- Save a compacted Lean object. Adapted from Loogle's `Pickle` module. -/
private def pickle {α : Type} (path : System.FilePath) (value : α) (key : Name) : IO Unit :=
  saveModuleData path key (unsafe unsafeCast value)

private unsafe def unpickle (α : Type) (path : System.FilePath) :
    IO (α × CompactedRegion) := do
  let (value, region) ← readModuleData path
  return (unsafeCast value, region)

private unsafe def loadPart (α : Type) (path : System.FilePath) (depHash : String) :
    IO (Option α) := do
  unless ← path.pathExists do return none
  try
    let ((storedHash, value), _) ← unsafe unpickle (String × α) path
    if storedHash == depHash then return some value
  catch _ => pure ()
  return none

private def depHash? (olean : System.FilePath) : IO (Option String) := do
  let path := olean.withExtension "trace"
  if ← path.pathExists then
    return (Json.parse (← IO.FS.readFile path) >>= (·.getObjValAs? String "depHash")).toOption
  let mut hashes := #[]
  for level in #[OLeanLevel.exported, OLeanLevel.server, OLeanLevel.private] do
    let path := level.adjustFileName olean
    if ← path.pathExists then
      hashes := hashes.push (toString (← Lake.computeFileHash path))
  return if hashes.isEmpty then none else some (String.intercalate ":" hashes.toList)

private def sourceNames (olean : System.FilePath) : IO (Std.HashSet String) := do
  let path := olean.withExtension "ilean"
  unless ← path.pathExists do return {}
  let ilean ← Server.Ilean.load path
  let mut names := ilean.decls.foldl (init := {}) fun names name _ => names.insert name
  for (ident, info) in ilean.references do
    if info.definition?.isSome then
      if let .const _ name := ident then names := names.insert name
  return names

private unsafe def readParts (olean : System.FilePath) :
    IO (Array (ModuleData × CompactedRegion) × Nat) := do
  let mut paths := #[olean]
  let mut visible := 0
  let server := OLeanLevel.server.adjustFileName olean
  if ← server.pathExists then
    paths := paths.push server
    visible := paths.size - 1
  let privatePath := OLeanLevel.private.adjustFileName olean
  if ← privatePath.pathExists then paths := paths.push privatePath
  return (← readModuleDataParts paths, visible)

private def collapseInternal (internal : NameMap NameSet) (dependencies : NameSet) : NameSet :=
  Id.run do
    let mut pending : Array Name := #[]
    for dependency in dependencies do pending := pending.push dependency
    let mut seen : NameHashSet := {}
    let mut result : NameSet := {}
    while let some name := pending.back? do
      pending := pending.pop
      unless seen.contains name do
        seen := seen.insert name
        match internal.find? name with
        | some dependencies =>
          for dependency in dependencies do pending := pending.push dependency
        | none => result := result.insert name
    return result

private unsafe def readFragment (moduleName : Name) (olean : System.FilePath) :
    IO (ModuleFragment × Array CompactedRegion) := do
  let (parts, visibleIndex) ← unsafe readParts olean
  let some (all, _) := parts.back? |
    throw <| IO.userError s!"empty module data for '{moduleName}'"
  let some (visible, _) := parts[visibleIndex]? |
    throw <| IO.userError s!"missing visible module data for '{moduleName}'"
  let source ← sourceNames olean
  let visibleNames := visible.constants.foldl (init := ({} : NameHashSet))
    fun names info => names.insert info.name
  let internal := all.constants.foldl (init := ({} : NameMap NameSet)) fun internal info =>
    if isBlackListed info.name || !visibleNames.contains info.name then
      internal.insert info.name info.getUsedConstantsAsSet
    else internal
  return ({
    imports := all.imports.map (·.module)
    declarations := visible.constants.filterMap fun info =>
      let name := info.name
      if source.contains name.toString && !isBlackListed name then
        some (name, collapseInternal internal info.getUsedConstantsAsSet)
      else none
  }, parts.map (·.2))

private def privateModule? (name : Name) : Option Name :=
  match privatePrefix? name with
  | some (.num p 0) => some (p.replacePrefix privateHeader .anonymous)
  | _ => none

private unsafe def addModuleConstant (env : Environment) (privateNames : NameHashSet)
    (info : ConstantInfo) : IO (Environment × NameHashSet) := do
  if env.contains info.name then return (env, privateNames)
  let isPrivate := isPrivateName info.name
  let userName := privateToUserName info.name
  if isPrivate && privateNames.contains userName then return (env, privateNames)
  let added ← env.addConstAsync info.name (.ofConstantInfo info)
    (exportedKind? := none) (reportExts := false) (checkMayContain := false)
  added.commitConst added.asyncEnv (some info)
  return (added.mainEnv, if isPrivate then privateNames.insert userName else privateNames)

unsafe def withModuleConstants {α : Type} (env : Environment) (moduleName : Name)
    (names : Array Name) (moduleOf? : Name → Option Name)
    (action : Environment → IO α) : IO α := do
  let (result, regions) ← show IO (α × Array CompactedRegion) from do
    let (parts, _) ← unsafe readParts (← findOLean moduleName)
    let some (data, _) := parts.back? |
      throw <| IO.userError s!"empty module data for '{moduleName}'"
    let mut regions := parts.map (·.2)
    let mut modules : NameMap ModuleData := {}
    modules := modules.insert moduleName data
    let mut env := env
    let mut privateNames : NameHashSet := {}
    for info in data.constants do
      (env, privateNames) ← unsafe addModuleConstant env privateNames info
    let mut pending := names.map (·, moduleName, true)
    let mut seen : NameHashSet := {}
    while let some (name, owner, scanValue) := pending.back? do
      pending := pending.pop
      if seen.contains name then continue
      seen := seen.insert name
      let data ← match modules.find? owner with
        | some data => pure data
        | none => do
          let (parts, _) ← unsafe readParts (← findOLean owner)
          let some (data, _) := parts.back? |
            throw <| IO.userError s!"empty module data for '{owner}'"
          regions := regions ++ parts.map (·.2)
          modules := modules.insert owner data
          pure data
      let some info := data.constants.find? (·.name == name) | continue
      (env, privateNames) ← unsafe addModuleConstant env privateNames info
      let dependencies :=
        if scanValue then info.getUsedConstantsAsSet
        else info.type.getUsedConstantsAsSet
      for dependency in dependencies do
        unless env.contains dependency || seen.contains dependency do
          let owner? :=
            if data.constants.any (·.name == dependency) then some owner
            else
              privateModule? dependency <|>
                (env.getModuleIdxFor? dependency >>=
                  fun index => env.header.moduleNames[index.toNat]?) <|>
                moduleOf? dependency
          if let some owner := owner? then pending := pending.push (dependency, owner, false)
    return (← action env, regions)
  regions.forM CompactedRegion.free
  return result

private unsafe def writeFragment (moduleName : Name) (olean path : System.FilePath)
    (hash : String) : IO Unit := do
  let regions ← show IO (Array CompactedRegion) from do
    let (fragment, regions) ← readFragment moduleName olean
    pickle path (hash, fragment) moduleName
    return regions
  regions.forM CompactedRegion.free

private unsafe def loadFragment (moduleName : Name) : IO ModuleFragment := do
  let olean ← findOLean moduleName
  let hash? ← depHash? olean
  let path := olean.withExtension s!"leanreach-module-{fragmentVersion}"
  if let some hash := hash? then
    if let some fragment ← unsafe loadPart ModuleFragment path hash then return fragment
    try
      writeFragment moduleName olean path hash
      if let some fragment ← unsafe loadPart ModuleFragment path hash then return fragment
    catch _ => pure ()
  return (← readFragment moduleName olean).1

unsafe def moduleNames (moduleName : Name) : IO (Array Name) :=
  return (← unsafe loadFragment moduleName).declarations.map (·.1)

private unsafe def buildIndex (roots : Array Name) : IO Index := do
  let mut pending := roots
  let mut seen : NameHashSet := {}
  let mut declarations := #[]
  while !pending.isEmpty do
    let mut batch := #[]
    while batch.size < 32 do
      let some moduleName := pending.back? | break
      pending := pending.pop
      unless seen.contains moduleName do
        seen := seen.insert moduleName
        batch := batch.push moduleName
    let tasks ← batch.mapM fun moduleName => IO.asTask (unsafe loadFragment moduleName)
    for (moduleName, task) in batch.zip tasks do
      let fragment ← IO.ofExcept task.get
      pending := pending ++ fragment.imports
      for (name, dependencies) in fragment.declarations do
        declarations := declarations.push (name, moduleName, dependencies)
  return Index.build declarations

unsafe def rootData (roots : Array Name) : IO (System.FilePath × String × Name) := do
  let some root := roots[0]? | throw <| IO.userError "no root modules"
  let olean ← findOLean root
  let some firstHash ← depHash? olean |
    throw <| IO.userError s!"could not hash root module '{root}'"
  if roots.size == 1 then return (olean, firstHash, root)
  let mut hashes := #[s!"{root}:{firstHash}"]
  for root in roots.extract 1 roots.size do
    let some hash ← depHash? (← findOLean root) |
      throw <| IO.userError s!"could not hash root module '{root}'"
    hashes := hashes.push s!"{root}:{hash}"
  return (olean, String.intercalate ":" hashes.toList, root)

unsafe def loadIndex (roots : Array Name) (loadRelations := true) : IO Index := do
  let (olean, depHash, root) ← unsafe rootData roots
  let stem := if roots.size == 1 then "leanreach" else "leanreach-roots"
  let catalogPath := olean.withExtension s!"{stem}-catalog-{catalogVersion}"
  let relationsPath := olean.withExtension s!"{stem}-relations-{relationsVersion}"
  if let some catalog ← unsafe loadPart Catalog catalogPath depHash then
    if !loadRelations then return Index.ofParts catalog (#[], #[])
    if let some relations ← unsafe loadPart Relations relationsPath depHash then
      return Index.ofParts catalog relations
  let index ← buildIndex roots
  try
    pickle catalogPath (depHash, index.catalog) (Name.str root "_leanreachCatalog")
    pickle relationsPath (depHash, index.relations) (Name.str root "_leanreachRelations")
  catch _ => IO.eprintln "leanreach: could not write root index cache"
  if loadRelations then return index
  return Index.ofParts index.catalog (#[], #[])

unsafe def loadPPModule (moduleName : Name) : IO (NameMap Declaration) := do
  let olean ← findOLean moduleName
  let some depHash ← depHash? olean | return {}
  let path := olean.withExtension s!"leanreach-pp-{ppVersion}"
  return (← unsafe loadPart (NameMap Declaration) path depHash).getD {}

private unsafe def ppRootData (roots : Array Name) (suffix : String) :
    IO (System.FilePath × String × Name) := do
  let (olean, depHash, root) ← unsafe rootData roots
  let stem := if roots.size == 1 then "root" else "roots"
  return (
    olean.withExtension s!"leanreach-pp-{stem}-{suffix}",
    depHash,
    root
  )

unsafe def isFullyPP (roots : Array Name) : IO Bool := do
  let (path, depHash, _) ← unsafe ppRootData roots (toString ppVersion)
  return (← unsafe loadPart Bool path depHash).getD false

unsafe def loadPP (moduleOf? : Name → Option Name)
    (names : Array Name) : IO (NameMap Declaration) := do
  let mut byModule : NameMap (Array Name) := {}
  for name in names do
    if let some moduleName := moduleOf? name then
      byModule := byModule.insert moduleName
        ((byModule.find? moduleName).getD #[] |>.push name)
  let mut declarations := {}
  for (moduleName, names) in byModule do
    let cached ← unsafe loadPPModule moduleName
    for name in names do
      if let some declaration := cached.find? name then
        declarations := declarations.insert name declaration
  return declarations

unsafe def savePPModule (moduleName : Name) (declarations : NameMap Declaration) :
    IO Unit := do
  let olean ← findOLean moduleName
  let some depHash ← depHash? olean | return
  let path := olean.withExtension s!"leanreach-pp-{ppVersion}"
  pickle path (depHash, declarations) (Name.str moduleName "_leanreachPP")

unsafe def savePP (before after : NameMap Declaration) : IO Unit := do
  let mut additions : NameMap (NameMap Declaration) := {}
  for (name, declaration) in after do
    unless before.contains name do
      let moduleName := declaration.moduleName.toName
      let moduleDeclarations := (additions.find? moduleName).getD {}
      additions := additions.insert moduleName (moduleDeclarations.insert name declaration)
  for (moduleName, added) in additions do
    let mut declarations ← unsafe loadPPModule moduleName
    for (name, declaration) in added do
      declarations := declarations.insert name declaration
    unsafe savePPModule moduleName declarations

unsafe def markFullyPP (roots : Array Name) : IO Unit := do
  let (path, depHash, root) ← unsafe ppRootData roots (toString ppVersion)
  pickle path (depHash, true) (Name.str root "_leanreachPPRoot")

end LeanReach.Cache
