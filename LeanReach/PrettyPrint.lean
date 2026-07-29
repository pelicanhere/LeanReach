import Lean.DeclarationRange
import Lean.PrettyPrinter.Delaborator.Builtins
import Lean.Structure
import Lean.Util.Path
import LeanReach.Declaration

namespace LeanReach

open Lean Meta

private abbrev SignatureCache := IO.Ref (NameMap String)

private def prettyPrintSignature (cache : SignatureCache) (name : Name) : MetaM String := do
  if let some signature := (← cache.get).find? name then return signature
  let signature ←
    try
      pure <| (← PrettyPrinter.ppSignature name).fmt.pretty (width := 10000)
    catch _ =>
      let some info := (← getEnv).find? name | return name.toString
      try
        pure s!"{name} : {(← PrettyPrinter.ppExpr info.type).pretty (width := 10000)}"
      catch _ =>
        pure s!"{name} : {info.type}"
  cache.modify (·.insert name signature)
  return signature

private def prettyPrintList (cache : SignatureCache) (label : String)
    (names : Array Name) : MetaM String := do
  if names.isEmpty then return ""
  let lines ← names.mapM (prettyPrintSignature cache)
  return s!"\n  {label}:\n    {String.intercalate "\n    " lines.toList}"

private def prettyPrintConstant (cache : SignatureCache) (name : Name)
    (info : ConstantInfo) : MetaM String := withCurrHeartbeats do
  let signature ← prettyPrintSignature cache name
  if info.isTheorem then return signature
  let isProposition ← try isProp info.type catch _ => pure false
  if isProposition then return signature
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
    (← prettyPrintList cache "fields" fields) ++
    (← prettyPrintList cache "constructors" inductiveInfo.ctors.toArray)

private def prettyPrintKnownDeclaration (cache : SignatureCache)
    (moduleName : Name) (file : Option String) (name : Name) : CoreM Declaration := do
  let env ← getEnv
  let some info := env.find? name | throwError "unknown declaration '{name}'"
  let range? := (← findDeclarationRanges? name).map (·.selectionRange)
  return {
    name := name.toString
    signature := ← MetaM.run' (prettyPrintConstant cache name info)
    moduleName := moduleName.toString
    file
    line := range?.map (·.pos.line) |>.getD 0
    column := range?.map (·.pos.column + 1) |>.getD 0
  }

def prettyPrintDeclaration (sourcePath : SearchPath) (name : Name) :
    CoreM Declaration := do
  let cache ← IO.mkRef {}
  let some moduleName ← findModuleOf? name | throwError "unknown module for '{name}'"
  let file := (← sourcePath.findModuleWithExt "lean" moduleName).map (·.toString)
  prettyPrintKnownDeclaration cache moduleName file name

def prettyPrintModule (sourcePath : SearchPath) (moduleName : Name)
    (names : Array Name) : CoreM (NameMap Declaration) := do
  let cache ← IO.mkRef {}
  let file := (← sourcePath.findModuleWithExt "lean" moduleName).map (·.toString)
  let mut declarations := {}
  for name in names do
    let declaration ←
      try prettyPrintKnownDeclaration cache moduleName file name
      catch error =>
        throwError m!"could not pretty-print '{name}' from '{moduleName}': {error.toMessageData}"
    declarations := declarations.insert name declaration
  return declarations

end LeanReach
