import LeanReach.PrettyPrint.Printer
import LeanReach.Runtime.Environment
import LeanReach.Runtime.ModuleData
import LeanReach.Runtime.Source

namespace LeanReach

open Lean Meta

unsafe def prettyPrintModuleIO (sourcePath : SearchPath) (env : Environment)
    (moduleName : Name) (names : Array Name) (moduleOf? : Name → Option Name) :
    IO (NameMap Declaration × PPTiming) := do
  let sourceStarted ← IO.monoNanosNow
  let source ← moduleSource sourcePath moduleName
  let sourceNanos := (← IO.monoNanosNow) - sourceStarted
  let env := env.setMainModule moduleName
  let print := fun env => do
    let planStarted ← IO.monoNanosNow
    let (bodies, signatureOverlay) ←
      unsafe runCore env (MetaM.run' (prettyPrintPlan names))
    let planNanos := (← IO.monoNanosNow) - planStarted
    let bodySet := bodies.foldl (init := ({} : NameHashSet))
      fun result name => result.insert name
    let action := fun env =>
      unsafe runCore env
        (MetaM.run' (prettyPrintModuleWithBodies moduleName source names bodySet))
    let ((declarations, timing), overlayNanos) ←
      if signatureOverlay.isEmpty && bodies.isEmpty then
        pure ((← action env), 0)
      else
        unsafe ModuleData.withPrivateOverlay env moduleName
          signatureOverlay bodies moduleOf? action
    return (declarations, {
      timing with
      privateOverlayNanos := overlayNanos
      signatureNanos := timing.signatureNanos + sourceNanos + planNanos
    })
  let missing := names.filter fun name => !env.contains name
  if missing.isEmpty then return ← print env
  let ((declarations, timing), overlayNanos) ←
    unsafe ModuleData.withPrivateOverlay env moduleName missing #[] moduleOf? print
  return (declarations, {
    timing with privateOverlayNanos := timing.privateOverlayNanos + overlayNanos
  })

end LeanReach
