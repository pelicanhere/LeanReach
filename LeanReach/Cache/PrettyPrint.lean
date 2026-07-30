import LeanReach.Cache.Storage
import LeanReach.PrettyPrint.Declaration

namespace LeanReach.Cache

open Lean

private def version := 3

unsafe def loadPPModule (moduleName : Name) : IO (NameMap Declaration) := do
  let olean ← findOLean moduleName
  let some depHash ← depHash? olean | return {}
  let path := olean.withExtension s!"leanreach-pp-{version}"
  return (← unsafe loadPart (NameMap Declaration) path depHash).getD {}

private unsafe def ppRootData (roots : Array Name) :
    IO (System.FilePath × String × Name) := do
  let (olean, depHash, root) ← unsafe rootData roots
  let stem := if roots.size == 1 then "root" else "roots"
  return (olean.withExtension s!"leanreach-pp-{stem}-{version}", depHash, root)

unsafe def isFullyPP (roots : Array Name) : IO Bool := do
  let (path, depHash, _) ← unsafe ppRootData roots
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
  let path := olean.withExtension s!"leanreach-pp-{version}"
  pickle path (depHash, declarations) (Name.str moduleName "_leanreachPP")

unsafe def savePP (before after : NameMap Declaration) : IO Unit := do
  let mut additions : NameMap (NameMap Declaration) := {}
  for (name, declaration) in after do
    unless before.contains name do
      let moduleName := declaration.moduleName.toName
      let moduleDeclarations := (additions.find? moduleName).getD {}
      additions := additions.insert moduleName (moduleDeclarations.insert name declaration)
  for (moduleName, added) in additions do
    unsafe savePPModule moduleName
      (Std.TreeMap.union (← unsafe loadPPModule moduleName) added)

unsafe def markFullyPP (roots : Array Name) : IO Unit := do
  let (path, depHash, root) ← unsafe ppRootData roots
  pickle path (depHash, true) (Name.str root "_leanreachPPRoot")

end LeanReach.Cache
