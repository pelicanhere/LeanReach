import LeanReach.Cache.Codec
import LeanReach.Search.Types
import Lean.Data.NameMap

namespace LeanReach.Cache

open Lean

structure ModuleFragment where
  imports : Array Name
  declarations : Array (Name × Dependencies Name)

namespace ModuleFragment

private abbrev Dictionary := Array Name × NameMap Nat

private def intern : Name → Dictionary → Nat × Dictionary
  | .anonymous, state => (0, state)
  | name@(.str parent _), state =>
    if let some id := state.2.find? name then (id, state)
    else
      let (_, dictionary, ids) := intern parent state
      let id := dictionary.size + 1
      (id, dictionary.push name, ids.insert name id)
  | name@(.num parent _), state =>
    if let some id := state.2.find? name then (id, state)
    else
      let (_, dictionary, ids) := intern parent state
      let id := dictionary.size + 1
      (id, dictionary.push name, ids.insert name id)

private def dictionary (fragment : ModuleFragment) : Dictionary := Id.run do
    let mut dictionary : Dictionary := (#[], {})
    for name in fragment.imports do dictionary := (intern name dictionary).2
    for (name, dependencies) in fragment.declarations do
      dictionary := (intern name dictionary).2
      for dependency in dependencies.all do
        dictionary := (intern dependency dictionary).2
    return dictionary

private def encodeName (ids : NameMap Nat) (bytes : ByteArray)
    (name : Name) : ByteArray :=
  let parent := (ids.find? name.getPrefix).getD 0
  match name with
  | .str _ value => Codec.pushBytes (Codec.pushNat bytes parent |>.push 0) value.toUTF8
  | .num _ value => Codec.pushNat (Codec.pushNat bytes parent |>.push 1) value
  | .anonymous => bytes

private def decodeRef (dictionary : Array Name)
    (bytes : ByteArray) : Codec.Decoder Name := do
  let id ← Codec.Decoder.readNat bytes
  if id == 0 then return .anonymous
  let some name := dictionary[id - 1]? | failure
  return name

def encode (fragment : ModuleFragment) (fingerprint : String) : ByteArray := Id.run do
  let (dictionary, ids) := fragment.dictionary
  let idOf := fun name => (ids.find? name).getD 0
  let mut bytes :=
    Codec.pushBytes
      (Codec.pushBytes ByteArray.empty "LRM11".toUTF8) fingerprint.toUTF8
  bytes := Codec.pushNat bytes dictionary.size
  for name in dictionary do bytes := encodeName ids bytes name
  bytes := Codec.pushNat bytes fragment.imports.size
  for name in fragment.imports do bytes := Codec.pushNat bytes (idOf name)
  bytes := Codec.pushNat bytes fragment.declarations.size
  for (name, dependencies) in fragment.declarations do
    bytes := Codec.pushNat bytes (idOf name)
    bytes := Codec.pushNat bytes dependencies.typeDeps.size
    for dependency in dependencies.typeDeps do
      bytes := Codec.pushNat bytes (idOf dependency)
    bytes := Codec.pushNat bytes dependencies.bodyDeps.size
    for dependency in dependencies.bodyDeps do
      bytes := Codec.pushNat bytes (idOf dependency)
  return bytes

def decode (bytes : ByteArray) (fingerprint : String) : Option ModuleFragment :=
  Codec.Decoder.runToEnd (bytes := bytes) do
    guard ((← Codec.Decoder.readBytes bytes) == "LRM11".toUTF8)
    guard ((← Codec.Decoder.readBytes bytes) == fingerprint.toUTF8)
    let nameCount ← Codec.Decoder.readNat bytes
    let mut dictionary := #[]
    for _ in [0:nameCount] do
      let parent ← decodeRef dictionary bytes
      let name ← match ← Codec.Decoder.readByte bytes with
        | 0 =>
          let some value := String.fromUTF8? (← Codec.Decoder.readBytes bytes) |
            failure
          pure (.str parent value)
        | 1 => pure (.num parent (← Codec.Decoder.readNat bytes))
        | _ => failure
      dictionary := dictionary.push name
    let importCount ← Codec.Decoder.readNat bytes
    let mut imports := #[]
    for _ in [0:importCount] do
      imports := imports.push (← decodeRef dictionary bytes)
    let declarationCount ← Codec.Decoder.readNat bytes
    let mut declarations := #[]
    for _ in [0:declarationCount] do
      let name ← decodeRef dictionary bytes
      let typeCount ← Codec.Decoder.readNat bytes
      let mut typeDeps := #[]
      for _ in [0:typeCount] do
        typeDeps := typeDeps.push (← decodeRef dictionary bytes)
      let bodyCount ← Codec.Decoder.readNat bytes
      let mut bodyDeps := #[]
      for _ in [0:bodyCount] do
        bodyDeps := bodyDeps.push (← decodeRef dictionary bytes)
      declarations := declarations.push (name, { typeDeps, bodyDeps })
    return { imports, declarations }

end ModuleFragment
end LeanReach.Cache
