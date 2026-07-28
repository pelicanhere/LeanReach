import Lake.Build.Trace
import Lake.Config.Module
import Lake.Load.Package

namespace LeanReach.Project

open Lean Lake System

private def cacheVersion := 4

private abbrev Metadata := Array Name × Bool

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
    let mathlib ← json.getObjValAs? Bool "mathlib"
    return (roots.map (·.toName), mathlib)
  return parsed.toOption

private def saveCached (path : FilePath) (hash : String) (roots : Array Name)
    (mathlib : Bool) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path <| (Json.mkObj [
    ("hash", toJson hash),
    ("roots", toJson <| roots.map (·.toString)),
    ("mathlib", toJson mathlib)
  ]).compress

private unsafe def loadConfig (dir sysroot : FilePath) : IO (Option Metadata) := do
  let lean ← LeanInstall.get sysroot (collocated := true)
  let lake := LakeInstall.ofLean lean
  let .ok lakeEnv ← (Env.compute lake lean (← findElanInstall?)).toBaseIO | return none
  let config : LoadConfig := { lakeEnv, wsDir := dir }
  let (some package, _) ← (loadPackage config).run? {} | return none
  let roots := package.leanLibs.flatMap (·.roots)
  return some (roots,
    package.depConfigs.any fun dependency => dependency.name == `mathlib)

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

unsafe def detectRoots (sysroot : FilePath) : IO (Array Name) := do
  let some dir ← findDir? | return #[]
  let some config ← configFile? dir | return #[]
  let hash := toString (← Lake.computeFileHash config)
  let cache := dir / ".lake" / s!"leanreach-project-{cacheVersion}"
  let metadata ←
    if let some metadata ← loadCached cache hash then pure (some metadata)
    else
      let metadata ← unsafe loadConfig dir sysroot
      if let some (roots, mathlib) := metadata then
        try saveCached cache hash roots mathlib catch _ => pure ()
      pure metadata
  let some (roots, mathlib) := metadata | return #[]
  let buildDir := dir / ".lake" / "build" / "lib" / "lean"
  let mut candidates := roots
  for root in roots do
    candidates := candidates ++
      (← builtSubmodules (Lean.modToFilePath buildDir root "") root)
  let mut built := #[]
  for moduleName in candidates do
    if !built.contains moduleName &&
        (← (Lean.modToFilePath buildDir moduleName "olean").pathExists) then
      built := built.push moduleName
  if mathlib && !built.contains `Mathlib then built := built.push `Mathlib
  return built

end LeanReach.Project
