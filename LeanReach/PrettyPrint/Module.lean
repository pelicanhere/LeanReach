import LeanReach.PrettyPrint.Printer
import LeanReach.Runtime.Environment
import LeanReach.Runtime.ModuleData

namespace LeanReach

open Lean

unsafe def prettyPrintModuleIO (sourcePath : SearchPath) (env : Environment)
    (moduleName : Name) (names : Array Name) (moduleOf? : Name → Option Name) :
    IO (NameMap Declaration × PPTiming) := do
  let preparationStarted ← IO.monoNanosNow
  let source ← moduleSource sourcePath moduleName
  let (bodies, signatureOverlay) ← unsafe runCore env (prettyPrintPlan names)
  let bodySet := bodies.foldl (init := ({} : NameHashSet))
    fun result name => result.insert name
  let preparationNanos := (← IO.monoNanosNow) - preparationStarted
  let print := fun env =>
    unsafe runCore env (prettyPrintModuleWithBodies moduleName source names bodySet)
  let ((declarations, timing), overlayNanos) ←
    if signatureOverlay.isEmpty && bodies.isEmpty then
      pure ((← print env), 0)
    else
      unsafe ModuleData.withPrivateOverlay env moduleName
        signatureOverlay bodies moduleOf? print
  return (declarations, {
    timing with
    privateOverlayNanos := overlayNanos
    signatureNanos := timing.signatureNanos + preparationNanos
  })

end LeanReach
