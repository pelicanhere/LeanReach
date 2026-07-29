import LeanReach

namespace LeanReach.Benchmarks

open Lean

private def sample [Inhabited α] (items : Array α) (count : Nat) : Array α :=
  if items.size ≤ count then items
  else (Array.range count).map fun index => items[index * items.size / count]!

unsafe def main (args : List String) : IO UInt32 := do
  let some count := args[0]?.bind (·.toNat?) |
    throw <| IO.userError "usage: PPProbe COUNT [OUTPUT]"
  let output? := args[1]?
  let sourcePath ← prepareEnvironment
  let index ← unsafe Cache.loadIndex #[`Mathlib] false
  let modules := index.declarationsByModule.toArray.qsort fun left right =>
    left.1.toString < right.1.toString
  let selected := sample modules count
  let importStarted ← IO.monoNanosNow
  let env ← importEnvironment (selected.map (·.1)) (leakEnv := true)
  let importNanos := (← IO.monoNanosNow) - importStarted
  let ppStarted ← IO.monoNanosNow
  let mut declarations := 0
  let mut lines := #[]
  let mut timing : PPTiming := { importNanos }
  for (moduleName, names) in selected do
    let (moduleDeclarations, elapsed) ← unsafe prettyPrintModuleIO
      sourcePath env moduleName names index.moduleOf?
    declarations := declarations + moduleDeclarations.size
    timing := timing + elapsed
    if output?.isSome then
      for (_, declaration) in moduleDeclarations do
        lines := lines.push (toJson declaration).compress
  let ppNanos := (← IO.monoNanosNow) - ppStarted
  if let some path := output? then
    IO.FS.writeFile (System.FilePath.mk path) (String.intercalate "\n" lines.toList)
  IO.println s!"modules={selected.size} declarations={declarations} \
    importMs={importNanos / 1000000} ppMs={ppNanos / 1000000} \
    totalMs={(importNanos + ppNanos) / 1000000} {timing.profile}"
  return 0

end LeanReach.Benchmarks

unsafe def main (args : List String) : IO UInt32 :=
  LeanReach.Benchmarks.main args
