import LeanReach.Cache.Storage
import LeanReach.PrettyPrint.Declaration

namespace LeanReach.Cache

open Lean

abbrev PPBatch := NameMap (NameMap Declaration)

private def ppPath (olean : System.FilePath) : System.FilePath :=
  -- Module PP cache format 3.
  olean.withExtension "leanreach-pp-3"

unsafe def loadPPModule (moduleName : Name) : IO (NameMap Declaration) := do
  let olean ← findOLean moduleName
  let some depHash ← depHash? olean | return {}
  return (← unsafe loadPart (NameMap Declaration) (ppPath olean) depHash).getD {}

private unsafe def ppRootData (roots : Array Name) :
    IO (System.FilePath × String × Name) := do
  let (olean, depHash, root) ← unsafe rootData roots
  let stem := if roots.size == 1 then "root" else "roots"
  -- Completed-view marker format 6.
  return (olean.withExtension s!"leanreach-pp-{stem}-6", depHash, root)

unsafe def isFullyPP (roots : Array Name) : IO Bool := do
  let (path, depHash, _) ← unsafe ppRootData roots
  return (← unsafe loadPart Bool path depHash).getD false

unsafe def loadPP (moduleOf? : Name → Option Name)
    (names : Array Name) : IO (NameMap Declaration) := do
  let mut modules : NameSet := {}
  for name in names do
    if let some moduleName := moduleOf? name then
      modules := modules.insert moduleName
  let mut declarations := {}
  for moduleName in modules do
    declarations := Std.TreeMap.union declarations
      (← unsafe loadPPModule moduleName)
  return declarations

unsafe def savePPModule (moduleName : Name) (declarations : NameMap Declaration) :
    IO Unit := do
  let olean ← findOLean moduleName
  let some depHash ← depHash? olean | return
  savePart (ppPath olean) depHash declarations (Name.str moduleName "_leanreachPP")

unsafe def savePP (additions : PPBatch) : IO Unit := do
  for (moduleName, added) in additions do
    unsafe savePPModule moduleName
      (Std.TreeMap.union (← unsafe loadPPModule moduleName) added)

unsafe def markFullyPP (roots : Array Name) : IO Unit := do
  let (path, depHash, root) ← unsafe ppRootData roots
  savePart path depHash true (Name.str root "_leanreachPPRoot")

end LeanReach.Cache
