import Lean.PrettyPrinter.Delaborator.Builtins
import Lean.PrettyPrinter
import Lean.Structure
import LeanReach.PrettyPrint.Declaration
import LeanReach.PrettyPrint.Timing

namespace LeanReach

open Lean Meta

private abbrev SignatureCache := IO.Ref (NameMap String)

private def structureFields (env : Environment) (name : Name) : Array Name :=
  if isStructure env name then
    getStructureFieldsFlattened env name (includeSubobjectFields := false)
      |>.filterMap (getProjFnForField? env name)
  else #[]

private def prettyPrintSignature (cache : SignatureCache) (name : Name) :
    MetaM (String × Nat) := do
  if let some signature := (← cache.get).find? name then return (signature, 0)
  let started ← IO.monoNanosNow
  let signature ←
    try
      pure <| (← PrettyPrinter.ppSignature name).fmt.pretty (width := 10000)
    catch _ =>
      match (← getEnv).find? name with
      | none => pure name.toString
      | some info =>
        try
          pure s!"{name} : {(← PrettyPrinter.ppExpr info.type).pretty (width := 10000)}"
        catch _ =>
          pure s!"{name} : {info.type}"
  cache.modify (·.insert name signature)
  return (signature, (← IO.monoNanosNow) - started)

private def prettyPrintList (cache : SignatureCache) (label : String)
    (names : Array Name) : MetaM (String × Nat) := do
  if names.isEmpty then return ("", 0)
  let mut lines := #[]
  let mut nanos := 0
  for name in names do
    let (line, elapsed) ← prettyPrintSignature cache name
    lines := lines.push line
    nanos := nanos + elapsed
  return (s!"\n  {label}:\n    {String.intercalate "\n    " lines.toList}", nanos)

private def prettyPrintConstant (cache : SignatureCache) (name : Name)
    (info : ConstantInfo) (includeBody : Bool) : MetaM (String × PPTiming) :=
    withCurrHeartbeats do
  let (signature, signatureNanos) ← prettyPrintSignature cache name
  if includeBody then
    if let some value := info.value? (allowOpaque := true) then
      let started ← IO.monoNanosNow
      let body ←
        try pure <| (← PrettyPrinter.ppExpr value).pretty (width := 100)
        catch _ => pure (toString value)
      return (
        s!"{signature} :=\n  {body.replace "\n" "\n  "}",
        { signatureNanos, bodyNanos := (← IO.monoNanosNow) - started }
      )
  let .inductInfo inductiveInfo := info |
    return (signature, { signatureNanos })
  let env ← getEnv
  let (fieldText, fieldNanos) ←
    prettyPrintList cache "fields" (structureFields env name)
  let (constructorText, constructorNanos) ←
    prettyPrintList cache "constructors" inductiveInfo.ctors.toArray
  return (
    signature ++ fieldText ++ constructorText,
    { signatureNanos := signatureNanos + fieldNanos + constructorNanos }
  )

private def needsBody (info : ConstantInfo) : MetaM Bool := do
  if match info with
    | .thmInfo _ => true
    | _ => false then return false
  if ← try isProp info.type catch _ => pure false then return false
  return info.value? (allowOpaque := true) |>.isSome

def prettyPrintPlan (names : Array Name) : MetaM (Array Name × Array Name) := do
  let env ← getEnv
  let mut bodies := #[]
  let mut overlay := #[]
  let mut overlaid : NameHashSet := {}
  for name in names do
    if let some info := env.find? name then
      if ← needsBody info then
        bodies := bodies.push name
      else
        if info.type.getUsedConstantsAsSet.any fun dependency => !env.contains dependency then
          overlay := overlay.push name
          overlaid := overlaid.insert name
        if let .inductInfo inductiveInfo := info then
          for auxiliary in structureFields env name ++ inductiveInfo.ctors.toArray do
            if !env.contains auxiliary && !overlaid.contains auxiliary then
              overlay := overlay.push auxiliary
              overlaid := overlaid.insert auxiliary
  return (bodies, overlay)

private def prettyPrintKnownDeclaration (cache : SignatureCache)
    (moduleName : String) (source : Option String × NameMap Lsp.Position) (name : Name)
    (includeBody : Bool) : MetaM (Declaration × PPTiming) := do
  let env ← getEnv
  let some info := env.find? name | throwError "unknown declaration '{name}'"
  let some file := source.1 |
    throwError "source file for '{name}' was not found"
  let some position := source.2.find? name |
    throwError "source position for '{name}' was not found"
  let (signature, timing) ← prettyPrintConstant cache name info includeBody
  return ({
      name := name.toString
      signature
      moduleName
      file := some file
      line := position.line + 1
      column := position.character + 1
    }, timing)

def prettyPrintModuleWithBodies (moduleName : Name)
    (source : Option String × NameMap Lsp.Position)
    (names : Array Name) (bodies : NameHashSet) :
    MetaM (NameMap Declaration × PPTiming) := do
  let cache ← IO.mkRef {}
  let moduleNameString := moduleName.toString
  let mut declarations := {}
  let mut timing := {}
  for name in names do
    let (declaration, elapsed) ←
      try prettyPrintKnownDeclaration cache moduleNameString source name (bodies.contains name)
      catch error =>
        throwError m!"could not pretty-print '{name}' from '{moduleName}': {error.toMessageData}"
    declarations := declarations.insert name declaration
    timing := timing + elapsed
  return (declarations, timing)

end LeanReach
