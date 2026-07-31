import Lake.Config.Module
import Lake.Load.Workspace

namespace LeanReach.Project

open Lean Lake System

structure Layout where
  leanPath : Array FilePath
  sourcePath : Array FilePath
  roots : Array Name

private initialize loadedLayouts : IO.Ref (Std.HashMap String Layout) ← IO.mkRef {}

private def configFile? (dir : FilePath) : IO (Option FilePath) := do
  for name in #[defaultLeanConfigFile, defaultTomlConfigFile] do
    let path := dir / name
    if ← path.pathExists then return some path
  return none

private partial def findDir? : IO (Option FilePath) := do
  let rec go (dir : FilePath) := do
    if (← configFile? dir).isSome then return some dir
    let some parent := dir.parent | return none
    if parent == dir then return none
    go parent
  go (← IO.currentDir)

private def fileStamp (path : FilePath) : IO String := do
  unless ← path.pathExists do return "<missing>"
  try
    let metadata ← path.metadata
    return s!"{metadata.modified.sec}:{metadata.modified.nsec}:{metadata.byteSize}"
  catch _ =>
    return "<unreadable>"

private def inputsFresh (paths stamps : Array String) : IO Bool := do
  if paths.size != stamps.size then return false
  for (path, stamp) in paths.zip stamps do
    unless (← fileStamp path) == stamp do return false
  return true

private def loadCached (path sysroot : FilePath) : IO (Option Layout) := do
  unless ← path.pathExists do return none
  let content ← try IO.FS.readFile path catch _ => return none
  let parsed : Except String (Layout × Array String × Array String) := do
    let json ← Json.parse content
    unless (← json.getObjValAs? String "sysroot") == sysroot.toString do
      throw "different Lean sysroot"
    let leanPath ← json.getObjValAs? (Array String) "leanPath"
    let sourcePath ← json.getObjValAs? (Array String) "sourcePath"
    let roots ← json.getObjValAs? (Array String) "roots"
    let inputs ← json.getObjValAs? (Array String) "inputs"
    let stamps ← json.getObjValAs? (Array String) "stamps"
    return ({
      leanPath := leanPath.map FilePath.mk
      sourcePath := sourcePath.map FilePath.mk
      roots := roots.map (·.toName)
    }, inputs, stamps)
  let some (layout, inputs, stamps) := parsed.toOption | return none
  return if ← inputsFresh inputs stamps then some layout else none

private def saveCached (path sysroot : FilePath) (layout : Layout)
    (inputs : Array FilePath) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  let stamps ← inputs.mapM fileStamp
  IO.FS.writeFile path <| (Json.mkObj [
    ("sysroot", toJson sysroot.toString),
    ("leanPath", toJson <| layout.leanPath.map (·.toString)),
    ("sourcePath", toJson <| layout.sourcePath.map (·.toString)),
    ("roots", toJson <| layout.roots.map (·.toString)),
    ("inputs", toJson <| inputs.map (·.toString)),
    ("stamps", toJson stamps)
  ]).compress

private def localizeEntry (workspace : Workspace) (packagesDir : FilePath)
    (entry : PackageEntry) : IO PackageEntry := do
  let dir ← match entry.src with
    | .path dir => pure dir
    | .git (subDir? := subDir?) .. => do
      let gitDir := packagesDir / entry.dirName
      pure <| subDir?.map (gitDir / ·) |>.getD gitDir
  let packageDir := workspace.dir / dir
  unless ← packageDir.isDir do
    throw <| IO.userError
      s!"dependency '{entry.name}' is not materialized at '{packageDir}'; run `lake update`"
  unless ← configFileExists (packageDir / entry.configFile) do
    throw <| IO.userError s!"dependency '{entry.name}' has no Lake config at '{packageDir}'"
  return { entry with src := .path dir }

private def localOverrides (workspace : Workspace) (manifest : Manifest) :
    IO (Array PackageEntry) := do
  let overrides ← Manifest.tryLoadEntries workspace.packageOverridesFile
  let entries : NameMap PackageEntry := ({} : NameMap PackageEntry)
    |>.insertMany (manifest.packages.map fun entry => (entry.name, entry))
    |>.insertMany (overrides.map fun entry => (entry.name, entry))
  let packagesDir := manifest.packagesDir?.getD workspace.relPkgsDir
  entries.valuesArray.mapM fun entry =>
    localizeEntry workspace packagesDir entry

private unsafe def loadWorkspace? (dir sysroot : FilePath) :
    IO (Option Workspace) := do
  let lean ← LeanInstall.get sysroot (collocated := true)
  let lake := LakeInstall.ofLean lean
  let .ok lakeEnv ← (Env.compute lake lean (← findElanInstall?)).toBaseIO | return none
  let config : LoadConfig := { lakeEnv, wsDir := dir }
  let (root?, rootLog) ← (loadWorkspaceRoot config).run? {}
  let some root := root? | do
    let message := rootLog.toString.trimAscii.copy
    throw <| IO.userError <| if message.isEmpty then
      "could not load the Lake project" else message
  let some manifest ← Manifest.load? root.manifestFile | do
    if root.root.depConfigs.isEmpty then return some root
    throw <| IO.userError "Lake manifest is missing; run `lake update`"
  let overrides ← localOverrides root manifest
  let (workspace?, log) ←
    (root.materializeDeps manifest config.leanOpts config.reconfigure overrides).run?
  let some workspace := workspace? | do
    let message := log.toString.trimAscii.copy
    throw <| IO.userError <| if message.isEmpty then
      "could not resolve the existing Lake workspace" else message
  return some workspace

private unsafe def workspaceLayout (workspace : Workspace) : IO Layout := do
  let mut roots := #[]
  let mut seen : NameHashSet := {}
  for library in workspace.root.leanLibs do
    unless ← library.srcDir.isDir do continue
    let modules ← (·.2) <$> StateT.run (s := #[]) do
      Lean.forEachModuleInDir library.srcDir fun name =>
        modify (·.push name)
    for name in modules do
      let module : Lake.Module := { lib := library, name }
      if library.isLocalModule name && !seen.contains name &&
          (← module.oleanFile.pathExists) then
        roots := roots.push name
        seen := seen.insert name
  if let some mathlib := workspace.findPackageByName? `mathlib then
    if let some module := mathlib.findModule? `Mathlib then
      if !seen.contains module.name && (← module.oleanFile.pathExists) then
        roots := roots.push module.name
  roots := roots.qsort Name.lt
  if roots.contains `Mathlib then
    roots := (roots.filter (· != `Mathlib)).push `Mathlib
  let sourcePath :=
    (workspace.root.leanLibs.map (·.srcDir) ++
      workspace.leanSrcPath.toArray ++ #[workspace.lakeEnv.lake.srcDir])
      |>.toList.eraseDups.toArray
  return {
    leanPath := workspace.leanPath.toArray
    sourcePath
    roots
  }

private def layoutInputs (dir : FilePath) (workspace : Workspace) :
    Array FilePath :=
  (workspace.packages.flatMap fun package =>
    #[package.configFile, package.manifestFile]) ++
      #[workspace.packageOverridesFile, dir / "lean-toolchain"]

unsafe def loadLayout? (sysroot : FilePath) (refresh := false) :
    IO (Option Layout) := do
  let some dir ← findDir? | return none
  let key := s!"{dir}\u0000{sysroot}"
  unless refresh do
    if let some layout := (← loadedLayouts.get).get? key then return some layout
  let cache := dir / ".lake" / "leanreach-project-9"
  unless refresh do
    if let some layout ← loadCached cache sysroot then
      loadedLayouts.modify (·.insert key layout)
      return some layout
  let some workspace ← unsafe loadWorkspace? dir sysroot | return none
  let layout ← unsafe workspaceLayout workspace
  try saveCached cache sysroot layout (layoutInputs dir workspace)
  catch _ => pure ()
  loadedLayouts.modify (·.insert key layout)
  return some layout

end LeanReach.Project
