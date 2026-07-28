import Lean.DeclarationRange
import Lean.PrettyPrinter.Delaborator.Builtins
import Lean.Structure
import Lean.Util.Path
import LeanReach.Declaration

namespace LeanReach

open Lean Meta

private def prettyPrintSignature (name : Name) : MetaM String := do
  try
    return (← PrettyPrinter.ppSignature name).fmt.pretty (width := 10000)
  catch _ =>
    let some info := (← getEnv).find? name | return name.toString
    try
      return s!"{name} : {(← PrettyPrinter.ppExpr info.type).pretty (width := 10000)}"
    catch _ =>
      return s!"{name} : {info.type}"

private def prettyPrintList (label : String) (names : Array Name) : MetaM String := do
  if names.isEmpty then return ""
  let lines ← names.mapM prettyPrintSignature
  return s!"\n  {label}:\n    {String.intercalate "\n    " lines.toList}"

private def prettyPrintConstant (name : Name) (info : ConstantInfo) : MetaM String :=
    withCurrHeartbeats do
  let signature ← prettyPrintSignature name
  let isProposition ← try isProp info.type catch _ => pure false
  if info.isTheorem || isProposition then return signature
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

private def prettyPrintKnownDeclaration (moduleName : Name) (file : Option String)
    (name : Name) : CoreM Declaration := do
  let env ← getEnv
  let some info := env.find? name | throwError "unknown declaration '{name}'"
  let range? := (← findDeclarationRanges? name).map (·.selectionRange)
  return {
    name := name.toString
    signature := ← MetaM.run' (prettyPrintConstant name info)
    moduleName := moduleName.toString
    file
    line := range?.map (·.pos.line) |>.getD 0
    column := range?.map (·.pos.column + 1) |>.getD 0
  }

def prettyPrintDeclaration (sourcePath : SearchPath) (name : Name) :
    CoreM Declaration := do
  let some moduleName ← findModuleOf? name | throwError "unknown module for '{name}'"
  let file := (← sourcePath.findModuleWithExt "lean" moduleName).map (·.toString)
  prettyPrintKnownDeclaration moduleName file name

def prettyPrintModule (sourcePath : SearchPath) (moduleName : Name)
    (names : Array Name) : CoreM (NameMap Declaration) := do
  let file := (← sourcePath.findModuleWithExt "lean" moduleName).map (·.toString)
  let mut declarations := {}
  for name in names do
    let declaration ←
      try prettyPrintKnownDeclaration moduleName file name
      catch error =>
        throwError m!"could not pretty-print '{name}' from '{moduleName}': {error.toMessageData}"
    declarations := declarations.insert name declaration
  return declarations

end LeanReach
