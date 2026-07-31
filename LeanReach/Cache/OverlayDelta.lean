import LeanReach.Cache.Overlay

namespace LeanReach.QueryOverlay.Incremental

open Lean

private structure ModuleState where
  name : Name
  outputHash : String
  imports : Array Name

structure Delta where
  removed : Array Entry
  added : Array Entry

private structure Manifest where
  roots : Array Name
  baseRoot : Name
  snapshotHash : String
  currentHash : String
  generation : Nat
  nextDelta : Nat
  deltaIds : Array Nat
  deltaEntries : Nat
  modules : Array ModuleState

private initialize loaded : IO.Ref (Std.HashMap String Relations) ← IO.mkRef {}

private def manifestPath (olean : System.FilePath) :=
  olean.withExtension "leanreach-query-overlay-manifest-5"

private def snapshotPath (olean : System.FilePath) (generation : Nat) :=
  olean.withExtension s!"leanreach-query-overlay-snapshot-5-{generation}"

private def deltaPath (olean : System.FilePath) (id : Nat) :=
  olean.withExtension s!"leanreach-query-overlay-delta-5-{id}"

private def manifestKey := "leanreach-query-overlay-manifest-5"

private def deltaKey (id : Nat) := s!"leanreach-query-overlay-delta-5-{id}"

private def moduleEntries (moduleName : Name)
    (fragment : Cache.ModuleFragment) : Array Entry :=
  fragment.declarations.map (fun (name, dependencies) => {
    target := { name, moduleName }
    dependencies := NameSet.ofArray dependencies
  }) |>.qsort fun left right => Name.lt left.target.name right.target.name

private def sameEntry (left right : Entry) : Bool :=
  left.target.name == right.target.name &&
    left.target.moduleName == right.target.moduleName &&
    left.dependencies.toArray == right.dependencies.toArray

private def changedEntries (previous current : Array Entry) : Delta := Id.run do
  let previousByName : NameMap Entry := ({} : NameMap Entry).insertMany <|
    previous.map fun entry => (entry.target.name, entry)
  let currentByName : NameMap Entry := ({} : NameMap Entry).insertMany <|
    current.map fun entry => (entry.target.name, entry)
  return {
    removed := previous.filter fun entry =>
      !(currentByName.find? entry.target.name).any (sameEntry entry)
    added := current.filter fun entry =>
      !(previousByName.find? entry.target.name).any (sameEntry entry)
  }

def Delta.applyRelations (delta : Delta) (relations : Relations) : Relations := Id.run do
  let mut entries := relations.entries
  let mut reverse := relations.reverse
  for entry in delta.removed do
    entries := entries.erase entry.target.name
    for dependency in entry.dependencies do
      reverse := reverse.alter dependency fun targets =>
        let remaining := (targets.getD #[]).filter
          fun target => target.name != entry.target.name ||
            target.moduleName != entry.target.moduleName
        if remaining.isEmpty then none else some remaining
  for entry in delta.added do
    entries := entries.insert entry.target.name entry
    for dependency in entry.dependencies do
      reverse := reverse.alter dependency fun targets =>
        let targets := targets.getD #[]
        let present := targets.any fun target =>
          target.name == entry.target.name &&
            target.moduleName == entry.target.moduleName
        some <| if present then targets
          else targets.push entry.target
  return { relations with entries, reverse }

private def Delta.size (delta : Delta) : Nat :=
  delta.removed.size + delta.added.size

private unsafe def loadManifest (olean : System.FilePath) : IO (Option Manifest) :=
  unsafe Cache.loadPart Manifest (manifestPath olean) manifestKey

private def saveManifest (olean : System.FilePath) (manifest : Manifest) : IO Unit :=
  Cache.savePart (manifestPath olean) manifestKey manifest
    `_leanreachQueryOverlayManifest

private unsafe def commitManifest (olean : System.FilePath)
    (previous current : Manifest) : IO Unit := do
  saveManifest olean current
  let active : NameMap String := ({} : NameMap String).insertMany <|
    current.modules.map fun state => (state.name, state.outputHash)
  for state in previous.modules do
    unless active.find? state.name == some state.outputHash do
      unsafe Cache.removeStoredModuleFragment state.name state.outputHash

private unsafe def loadSnapshot (olean : System.FilePath)
    (manifest : Manifest) : IO (Option Relations) := do
  let some snapshot ← unsafe Cache.loadPart Relations
      (snapshotPath olean manifest.generation) manifest.snapshotHash |
    return none
  let mut relations := snapshot
  for id in manifest.deltaIds do
    let some delta ← unsafe Cache.loadPart Delta (deltaPath olean id) (deltaKey id) |
      return none
    relations := delta.applyRelations relations
  return some relations

private def saveSnapshot (olean : System.FilePath) (generation : Nat)
    (hash : String) (relations : Relations) : IO Unit :=
  Cache.savePart (snapshotPath olean generation) hash relations
    `_leanreachQueryOverlaySnapshot

private def removeArtifacts (olean : System.FilePath) (manifest : Manifest) : IO Unit := do
  Cache.removeFileIfExists (snapshotPath olean manifest.generation)
  manifest.deltaIds.forM fun id => Cache.removeFileIfExists (deltaPath olean id)

private def moduleState (moduleName : Name) (outputHash : String)
    (fragment : Cache.ModuleFragment) : ModuleState :=
  { name := moduleName, outputHash, imports := fragment.imports }

private unsafe def statesOf
    (fragments : Array (Name × Cache.ModuleFragment)) : IO (Array ModuleState) :=
  fragments.mapM fun (moduleName, fragment) => do
    let olean ← findOLean moduleName
    let some outputHash ← Cache.oleanHash? olean |
      throw <| IO.userError s!"could not hash module output '{moduleName}'"
    return moduleState moduleName outputHash fragment

private unsafe def changedModules (manifest : Manifest) :
    IO (Option (Array ModuleState × Delta)) := do
  try
    let previous : NameMap ModuleState := ({} : NameMap ModuleState).insertMany <|
      manifest.modules.map fun state => (state.name, state)
    let some base ← unsafe SearchCache.loadTable #[manifest.baseRoot] | return none
    let mut pending := #[]
    let mut seen : NameHashSet :=
      (Std.HashSet.ofArray base.modules).insert manifest.baseRoot
    for root in manifest.roots do
      unless seen.contains root do
        seen := seen.insert root
        pending := pending.push root
    let mut current : NameMap ModuleState := {}
    let mut removed := #[]
    let mut added := #[]
    while let some moduleName := pending.back? do
      pending := pending.pop
      let olean ← findOLean moduleName
      let some outputHash ← Cache.oleanHash? olean | return none
      let (state, imports) ← match previous.find? moduleName with
        | some state => do
          if state.outputHash == outputHash then
            pure (state, state.imports)
          else
            let some old ← unsafe Cache.storedModuleFragment
                moduleName state.outputHash | return none
            let fresh ← unsafe Cache.moduleFragment moduleName
            let freshState := moduleState moduleName outputHash fresh
            let oldEntries := moduleEntries moduleName old
            let freshEntries := moduleEntries moduleName fresh
            let changed := changedEntries oldEntries freshEntries
            removed := removed ++ changed.removed
            added := added ++ changed.added
            pure (freshState, fresh.imports)
        | none => do
          let fresh ← unsafe Cache.moduleFragment moduleName
          let freshState := moduleState moduleName outputHash fresh
          added := added ++ moduleEntries moduleName fresh
          pure (freshState, fresh.imports)
      current := current.insert moduleName state
      for imported in imports do
        unless seen.contains imported do
          seen := seen.insert imported
          pending := pending.push imported
    for (moduleName, state) in previous do
      unless current.contains moduleName do
        let some old ← unsafe Cache.storedModuleFragment
            moduleName state.outputHash | return none
        removed := removed ++ moduleEntries moduleName old
    return some (current.valuesArray, { removed, added })
  catch _ =>
    return none

private def shouldCompact (manifest : Manifest) (relations : Relations)
    (delta : Delta) : Bool :=
  manifest.deltaIds.size + 1 ≥ 8 ||
    manifest.deltaEntries + delta.size > max 256 (relations.entries.size / 4)

private unsafe def refresh (olean : System.FilePath) (currentHash : String)
    (manifest : Manifest) : IO (Option Relations) := do
  let some (modules, delta) ← unsafe changedModules manifest | return none
  let some previous ← unsafe loadSnapshot olean manifest | return none
  let relations := delta.applyRelations previous
  if delta.size == 0 then
    let updated := { manifest with currentHash, modules }
    unsafe commitManifest olean manifest updated
    return some relations
  if shouldCompact manifest previous delta then
    let generation := manifest.generation + 1
    saveSnapshot olean generation currentHash relations
    let updated := {
      manifest with
      snapshotHash := currentHash
      currentHash
      generation
      deltaIds := #[]
      deltaEntries := 0
      modules
    }
    unsafe commitManifest olean manifest updated
    removeArtifacts olean manifest
    return some relations
  let id := manifest.nextDelta
  Cache.savePart (deltaPath olean id) (deltaKey id) delta
    `_leanreachQueryOverlayDelta
  let updated := {
    manifest with
    currentHash
    nextDelta := id + 1
    deltaIds := manifest.deltaIds.push id
    deltaEntries := manifest.deltaEntries + delta.size
    modules
  }
  unsafe commitManifest olean manifest updated
  return some relations

private unsafe def loadRelationsView (roots : Array Name) : IO (Option Relations) := do
  let (olean, currentHash, _) ← unsafe Cache.rootData roots
  let key := Cache.loadedKey (manifestPath olean) currentHash
  if let some relations := (← loaded.get).get? key then return some relations
  let some manifest ← unsafe loadManifest olean | return none
  unless manifest.roots == roots do return none
  let result : Option Relations ←
    if manifest.currentHash == currentHash then do
      unsafe loadSnapshot olean manifest
    else
      unsafe refresh olean currentHash manifest
  let some relations := result | return none
  loaded.modify (·.insert key relations)
  return some relations

unsafe def loadCatalog (roots : Array Name) : IO (Option Catalog) :=
  return (← unsafe loadRelationsView roots).map (·.catalog)

unsafe def loadRelations (roots : Array Name) : IO (Option Relations) :=
  unsafe loadRelationsView roots

unsafe def saveBaseline (roots : Array Name)
    (relations : Relations)
    (fragments : Array (Name × Cache.ModuleFragment)) : IO Unit := do
  let (olean, currentHash, _) ← unsafe Cache.rootData roots
  let previous ← unsafe loadManifest olean
  let generation := (previous.map (·.generation + 1)).getD 0
  saveSnapshot olean generation currentHash relations
  let manifest : Manifest := {
    roots
    baseRoot := relations.baseRoot
    snapshotHash := currentHash
    currentHash
    generation
    nextDelta := 0
    deltaIds := #[]
    deltaEntries := 0
    modules := ← unsafe statesOf fragments
  }
  if let some previous := previous then
    unsafe commitManifest olean previous manifest
    removeArtifacts olean previous
  else
    saveManifest olean manifest
  loaded.modify (·.insert (Cache.loadedKey (manifestPath olean) currentHash) relations)

end LeanReach.QueryOverlay.Incremental
