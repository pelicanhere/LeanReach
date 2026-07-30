import LeanReach.Cache
import LeanReach.Index
import LeanReach.ModuleData
import LeanReach.SourceInfo

namespace LeanReach.Cache

open Lean

/-
Adapted from Loogle/BlackListed.lean.
Copyright (c) 2019 Robert Y. Lewis and contributors.
Released under the Apache License 2.0.
-/

/-- Hide generated implementation details that can still have source ranges. -/
private def isBlacklisted (name : Name) : Bool :=
  name.isInternal || name.isInternalDetail || isPrivateName name

private def catalogVersion := 6
private def relationsVersion := 7
private def fragmentVersion := 6

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
  let (parts, visibleIndex) ← unsafe ModuleData.readParts olean
  let some (all, _) := parts.back? |
    throw <| IO.userError s!"empty module data for '{moduleName}'"
  let some (visible, _) := parts[visibleIndex]? |
    throw <| IO.userError s!"missing visible module data for '{moduleName}'"
  let source ← sourceNames olean
  let visibleNames := visible.constants.foldl (init := ({} : NameHashSet))
    fun names info => names.insert info.name
  let (constants, internal) := all.constants.foldl
      (init := (({} : NameMap ConstantInfo), ({} : NameMap NameSet))) fun state info =>
    let constants := state.1.insert info.name info
    let internal :=
      if isBlacklisted info.name || !visibleNames.contains info.name then
        state.2.insert info.name info.getUsedConstantsAsSet
      else state.2
    (constants, internal)
  return ({
    imports := all.imports.map (·.module)
    declarations := visible.constants.filterMap fun visibleInfo =>
      let name := visibleInfo.name
      if source.contains name.toString && !isBlacklisted name then
        let info := (constants.find? name).getD visibleInfo
        some (name, collapseInternal internal info.getUsedConstantsAsSet)
      else none
  }, parts.map (·.2))

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

unsafe def moduleNames (moduleName : Name) : IO (Array Name) := do
  return (← unsafe loadFragment moduleName).declarations.map (·.1)

unsafe def moduleDeclarations (moduleName : Name) : IO (Array (Name × NameSet)) := do
  return (← unsafe loadFragment moduleName).declarations

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

unsafe def loadIndex (roots : Array Name) (loadRelations := true) : IO Index := do
  let (olean, depHash, root) ← unsafe rootData roots
  let stem := if roots.size == 1 then "leanreach" else "leanreach-roots"
  let catalogPath := olean.withExtension s!"{stem}-catalog-{catalogVersion}"
  let relationsPath := olean.withExtension s!"{stem}-relations-{relationsVersion}"
  if let some catalog ← unsafe loadPart Catalog catalogPath depHash then
    if !loadRelations then return Index.ofParts catalog default
    if let some relations ← unsafe loadPart Relations relationsPath depHash then
      return Index.ofParts catalog relations
  let index ← buildIndex roots
  try
    pickle catalogPath (depHash, index.catalog) (Name.str root "_leanreachCatalog")
    pickle relationsPath (depHash, index.relations) (Name.str root "_leanreachRelations")
  catch _ => IO.eprintln "leanreach: could not write root index cache"
  if loadRelations then return index
  return Index.ofParts index.catalog default

end LeanReach.Cache
