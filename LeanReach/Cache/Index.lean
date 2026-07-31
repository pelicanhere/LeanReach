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

private unsafe def foldClosure {α : Type} (roots : Array Name)
    (excluded : NameHashSet) (initial : α)
    (visit : α → Name → Array (Name × NameSet) → IO α) : IO α := do
  let mut pending := #[]
  let mut seen := excluded
  let mut result := initial
  for root in roots do
    unless seen.contains root do
      seen := seen.insert root
      pending := pending.push root
  while !pending.isEmpty do
    let mut batch := #[]
    while batch.size < 32 do
      let some moduleName := pending.back? | break
      pending := pending.pop
      batch := batch.push moduleName
    let tasks ← batch.mapM fun moduleName => IO.asTask (unsafe moduleData moduleName)
    for (moduleName, task) in batch.zip tasks do
      let (imports, moduleDeclarations) ← IO.ofExcept task.get
      result ← visit result moduleName moduleDeclarations
      for imported in imports do
        unless seen.contains imported do
          seen := seen.insert imported
          pending := pending.push imported
  return result

unsafe def moduleClosure (roots : Array Name) (excluded : NameHashSet := {}) :
    IO (Array (Name × Array (Name × NameSet))) :=
  unsafe foldClosure roots excluded #[] fun modules moduleName declarations =>
    pure (modules.push (moduleName, declarations))

unsafe def materializeIndex (roots : Array Name) : IO Index := do
  let declarations ← unsafe foldClosure roots {} ({} : Index.Declarations)
      fun result moduleName entries =>
    pure <| entries.foldl (init := result) fun result (name, dependencies) =>
      result.add name moduleName dependencies
  return Index.buildFrom declarations

end LeanReach.Cache
