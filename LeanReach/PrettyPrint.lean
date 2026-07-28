import Lean.DeclarationRange
import Lean.PrettyPrinter.Delaborator.Builtins
import Lean.Structure
import Lean.Util.Path
import LeanReach.Declaration

namespace LeanReach

open Lean Meta

private def prettyPrintSignature (name : Name) : MetaM String := do
  try
    let expression ← mkConstWithLevelParams name
    let (stx, _) ← PrettyPrinter.delabCore expression
      (delab := PrettyPrinter.Delaborator.delabConstWithSignature (universes := false))
    return (← PrettyPrinter.ppTerm ⟨stx⟩).pretty (width := 10000)
  catch _ =>
    let info ← getConstInfo name
    return s!"{name} : {(← PrettyPrinter.ppExpr info.type).pretty (width := 10000)}"

private def prettyPrintList (label : String) (names : Array Name) : MetaM String := do
  if names.isEmpty then return ""
  let lines ← names.mapM prettyPrintSignature
  return s!"\n  {label}:\n    {String.intercalate "\n    " lines.toList}"

private def prettyPrintConstant (name : Name) (info : ConstantInfo) : MetaM String :=
    withCurrHeartbeats do
  let signature ← prettyPrintSignature name
  if info.isTheorem || (← isProp info.type) then return signature
  if let some value := info.value? (allowOpaque := true) then
    let body ←
      try pure <| (← PrettyPrinter.ppExpr value).pretty (width := 100)
      catch _ => pure (toString value)
    return s!"{signature} :=\n  {body.replace "\n" "\n  "}"
  let .inductInfo inductiveInfo := info | return signature
  let env ← getEnv
  let fields :=
    if isStructure env name then
      getStructureFieldsFlattened env name (includeSubobjectFields := false)
        |>.filterMap (getProjFnForField? env name)
    else #[]
  return signature ++
    (← prettyPrintList "fields" fields) ++
    (← prettyPrintList "constructors" inductiveInfo.ctors.toArray)

def prettyPrintDeclaration (sourcePath : SearchPath) (name : Name) :
    CoreM Declaration := do
  let env ← getEnv
  let some info := env.find? name | throwError "unknown declaration '{name}'"
  let moduleName? ← findModuleOf? name
  let file? ← moduleName?.mapM fun moduleName =>
    return (← sourcePath.findModuleWithExt "lean" moduleName).map (·.toString)
  let range? := (← findDeclarationRanges? name).map (·.selectionRange)
  return {
    name := name.toString
    signature := ← MetaM.run' (prettyPrintConstant name info)
    moduleName := moduleName?.map (·.toString) |>.getD ""
    file := file?.getD none
    line := range?.map (·.pos.line) |>.getD 0
    column := range?.map (·.pos.column + 1) |>.getD 0
  }

end LeanReach
