import Lean.Server.References
import Lean.Util.Path
import LeanReach.Query.Context

namespace LeanReach.Query

open Lean

def ileanPath? (moduleName : Name) : IO (Option System.FilePath) := do
  try
    let path := (← findOLean moduleName).withExtension "ilean"
    return if ← path.pathExists then some path else none
  catch _ =>
    return none

def loadIlean? (moduleName : Name) : IO (Option Server.Ilean) := do
  let some path ← ileanPath? moduleName | return none
  return some (← Server.Ilean.load path)

def sourceDependencies (ilean : Server.Ilean) (parent : Name) : NameSet := Id.run do
  let parentName := nameString parent
  let mut dependencies : NameSet := {}
  for (ident, info) in ilean.references do
    let .const _ dependencyName := ident | continue
    if info.usages.any fun usage => usage.parentDecl? == some parentName then
      dependencies := dependencies.insert dependencyName.toName
  return dependencies

private def parentN (path : System.FilePath) : Nat → Option System.FilePath
  | 0 => some path
  | count + 1 => path.parent.bind fun parent => parentN parent count

/--
Build a source search path from both `LEAN_SRC_PATH` and Lake's `.olean` roots. Lake reliably sets
`LEAN_PATH` for executables, but does not set `LEAN_SRC_PATH` on every platform.
-/
def sourceSearchPath : IO SearchPath := do
  let mut sources ← getSrcSearchPath
  for oleanRoot in (← searchPathRef.get) do
    -- Lake package/project layout: ROOT/.lake/build/lib/lean
    if let some packageRoot := parentN oleanRoot 4 then
      sources := sources ++ [packageRoot]
    -- Lean toolchain layout: SYSROOT/lib/lean -> SYSROOT/src/lean
    if let some sysroot := parentN oleanRoot 2 then
      sources := sources ++ [sysroot / "src" / "lean"]
  return sources

end LeanReach.Query
