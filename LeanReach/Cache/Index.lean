import LeanReach.Cache.Storage
import LeanReach.Runtime.ModuleData
import LeanReach.Runtime.Source
import LeanReach.Search.Index

namespace LeanReach.Cache

open Lean

/-
Adapted from Loogle/BlackListed.lean.
Copyright (c) 2019 Robert Y. Lewis and contributors.
Released under the Apache License 2.0.
-/

/-- Hide generated implementation details that can still have source ranges. -/
private def isBlacklisted (name : Name) : Bool :=
  (privateToUserName name).isInternalDetail

private structure ModuleFragment where
  imports : Array Name
  declarations : Array (Name × NameSet)

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
  let parts ← unsafe ModuleData.readParts olean
  let some (all, _) := parts.back? |
    throw <| IO.userError s!"empty module data for '{moduleName}'"
  let regions := parts.map (·.2)
  try
    let source ← sourceNames olean
    let internal := all.constants.foldl (init := ({} : NameMap NameSet)) fun result info =>
      if source.contains info.name && !isBlacklisted info.name then result
      else result.insert info.name info.getUsedConstantsAsSet
    return ({
      imports := all.imports.map (·.module)
      declarations := all.constants.filterMap fun visibleInfo =>
        let name := visibleInfo.name
        if source.contains name && !isBlacklisted name then
          some (name, collapseInternal internal visibleInfo.getUsedConstantsAsSet)
        else none
    }, regions)
  catch error =>
    regions.forM CompactedRegion.free
    throw error

private unsafe def writeFragment (moduleName : Name) (olean path : System.FilePath)
    (hash : String) : IO Unit := do
  let (fragment, regions) ← readFragment moduleName olean
  try
    savePart path hash fragment moduleName
  finally
    regions.forM CompactedRegion.free

private unsafe def loadFragment (moduleName : Name) : IO ModuleFragment := do
  let olean ← findOLean moduleName
  let hash? ← depHash? olean
  -- Module-fragment cache format 7.
  let path := olean.withExtension "leanreach-module-7"
  if let some hash := hash? then
    if let some fragment ← unsafe loadPart ModuleFragment path hash then return fragment
    try
      writeFragment moduleName olean path hash
      if let some fragment ← unsafe loadPart ModuleFragment path hash then return fragment
    catch _ => pure ()
  return (← readFragment moduleName olean).1

unsafe def moduleData (moduleName : Name) :
    IO (Array Name × Array (Name × NameSet)) := do
  let fragment ← unsafe loadFragment moduleName
  return (fragment.imports, fragment.declarations)

unsafe def moduleNames (moduleName : Name) : IO (Array Name) :=
  return (← unsafe moduleData moduleName).2.map (·.1)

unsafe def moduleClosure (roots : Array Name) (excluded : NameHashSet := {}) :
    IO (Array (Name × Array (Name × NameSet))) := do
  let mut pending := #[]
  let mut seen := excluded
  for root in roots do
    unless seen.contains root do
      seen := seen.insert root
      pending := pending.push root
  let mut modules := #[]
  while !pending.isEmpty do
    let mut batch := #[]
    while batch.size < 32 do
      let some moduleName := pending.back? | break
      pending := pending.pop
      batch := batch.push moduleName
    let tasks ← batch.mapM fun moduleName => IO.asTask (unsafe moduleData moduleName)
    for (moduleName, task) in batch.zip tasks do
      let (imports, moduleDeclarations) ← IO.ofExcept task.get
      modules := modules.push (moduleName, moduleDeclarations)
      for imported in imports do
        unless seen.contains imported do
          seen := seen.insert imported
          pending := pending.push imported
  return modules

private unsafe def buildIndex (roots : Array Name) : IO Index := do
  let mut declarations := #[]
  for (moduleName, moduleDeclarations) in ← unsafe moduleClosure roots do
    for (name, dependencies) in moduleDeclarations do
      declarations := declarations.push (name, moduleName, dependencies)
  return Index.build declarations

unsafe def loadIndex (roots : Array Name) (loadRelations := true) : IO Index := do
  let (olean, depHash, root) ← unsafe rootData roots
  let stem := if roots.size == 1 then "leanreach" else "leanreach-roots"
  -- Root catalog format 7; relation-index format 8.
  let catalogPath := olean.withExtension s!"{stem}-catalog-7"
  let relationsPath := olean.withExtension s!"{stem}-relations-8"
  if let some catalog ← unsafe loadPart Catalog catalogPath depHash then
    if !loadRelations then return Index.ofParts catalog default
    if let some relations ← unsafe loadPart Relations relationsPath depHash then
      return Index.ofParts catalog relations
  let index ← buildIndex roots
  try
    savePart catalogPath depHash index.catalog (Name.str root "_leanreachCatalog")
    savePart relationsPath depHash index.toRelations (Name.str root "_leanreachRelations")
  catch _ => IO.eprintln "leanreach: could not write root index cache"
  if loadRelations then return index
  return Index.ofParts index.catalog default

end LeanReach.Cache
