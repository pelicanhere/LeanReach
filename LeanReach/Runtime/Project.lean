import Lake.Build.Trace
import Lake.Config.Module
import Lake.Load.Package

namespace LeanReach.Project

open Lean Lake System

private def cacheVersion := 7

private abbrev Metadata := Array Name × Array String × Bool × Array Name

private def configFile? (dir : FilePath) : IO (Option FilePath) := do
  for name in #[defaultLeanConfigFile, defaultTomlConfigFile] do
    let path := dir / name
    if ← path.pathExists then return some path
  return none

partial def findDir? : IO (Option FilePath) := do
  let rec go (dir : FilePath) := do
    if (← configFile? dir).isSome then return some dir
    let some parent := dir.parent | return none
    if parent == dir then return none
    go parent
  go (← IO.currentDir)

private def loadCached (path : FilePath) (hash : String) : IO (Option Metadata) := do
  unless ← path.pathExists do return none
  let content ← IO.FS.readFile path
  let parsed : Except String Metadata := do
    let json ← Json.parse content
    unless (← json.getObjValAs? String "hash") == hash do
      throw "stale project cache"
    let roots ← json.getObjValAs? (Array String) "roots"
    let sourceDirs ← json.getObjValAs? (Array String) "sourceDirs"
    let mathlib ← json.getObjValAs? Bool "mathlib"
    let built ← json.getObjValAs? (Array String) "built"
    return (roots.map (·.toName), sourceDirs, mathlib, built.map (·.toName))
  return parsed.toOption

private def saveCached (path : FilePath) (hash : String) (roots : Array Name)
    (sourceDirs : Array String) (mathlib : Bool) (built : Array Name) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path <| (Json.mkObj [
    ("hash", toJson hash),
    ("roots", toJson <| roots.map (·.toString)),
    ("sourceDirs", toJson sourceDirs),
    ("mathlib", toJson mathlib),
    ("built", toJson <| built.map (·.toString))
  ]).compress

private unsafe def loadConfig (dir sysroot : FilePath) : IO (Option Metadata) := do
  let lean ← LeanInstall.get sysroot (collocated := true)
  let lake := LakeInstall.ofLean lean
  let .ok lakeEnv ← (Env.compute lake lean (← findElanInstall?)).toBaseIO | return none
  let config : LoadConfig := { lakeEnv, wsDir := dir }
  let (some package, _) ← (loadPackage config).run? {} | return none
  let libraries := package.leanLibs
  let roots := libraries.flatMap (·.roots)
  return some (roots, libraries.map (·.srcDir.toString),
    package.depConfigs.any fun dependency => dependency.name == `mathlib, #[])

private partial def builtSubmodules (dir : FilePath) (base : Name) : IO (Array Name) := do
  unless ← dir.isDir do return #[]
  let mut modules := #[]
  for entry in ← dir.readDir do
    let name := Name.str base (FilePath.withExtension entry.fileName "").toString
    if ← entry.path.isDir then
      modules := modules ++ (← builtSubmodules entry.path name)
    else if entry.path.extension == some "olean" then
      modules := modules.push name
  return modules

unsafe def detectRoots (sysroot : FilePath) (refresh := false) : IO (Array Name) := do
  let some dir ← findDir? | return #[]
  let some config ← configFile? dir | return #[]
  let hash := toString (← Lake.computeFileHash config)
  let cache := dir / ".lake" / s!"leanreach-project-{cacheVersion}"
  let cached ← loadCached cache hash
  if !refresh then
    if let some (_, _, _, built) := cached then return built
  let metadata ← cached.map some |>.getDM (unsafe loadConfig dir sysroot)
  let some (roots, sourceDirs, mathlib, _) := metadata | return #[]
  let buildDir := dir / ".lake" / "build" / "lib" / "lean"
  let mut candidates := roots
  for root in roots do
    candidates := candidates ++
      (← builtSubmodules (Lean.modToFilePath buildDir root "") root)
  let mut built := #[]
  for moduleName in candidates do
    let mut hasSource := false
    for sourceDir in sourceDirs do
      if ← (Lean.modToFilePath (FilePath.mk sourceDir) moduleName "lean").pathExists then
        hasSource := true
        break
    if hasSource && !built.contains moduleName &&
        (← (Lean.modToFilePath buildDir moduleName "olean").pathExists) then
      built := built.push moduleName
  built := built.qsort Name.lt
  if mathlib && !built.contains `Mathlib then built := built.push `Mathlib
  try saveCached cache hash roots sourceDirs mathlib built catch _ => pure ()
  return built

end LeanReach.Project
