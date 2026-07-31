namespace LeanReach.Cache.Codec

def pushNat (bytes : ByteArray) (value : Nat) : ByteArray := Id.run do
  let mut bytes := bytes
  let mut value := value
  while value ≥ 128 do
    bytes := bytes.push (UInt8.ofNat (value % 128 + 128))
    value := value / 128
  return bytes.push (UInt8.ofNat value)

def readNat (bytes : ByteArray) (start : Nat) : Option (Nat × Nat) := Id.run do
  let mut position := start
  let mut value := 0
  let mut scale := 1
  for _ in [0:10] do
    let some byte := bytes[position]? | return none
    position := position + 1
    value := value + byte.toNat % 128 * scale
    if byte < 128 then return some (value, position)
    scale := scale * 128
  return none

def pushUInt32 (bytes : ByteArray) (value : UInt32) : ByteArray :=
  pushNat bytes value.toNat

def readUInt32 (bytes : ByteArray) (start : Nat) :
    Option (UInt32 × Nat) := do
  let (value, position) ← readNat bytes start
  if value < 4294967296 then some (value.toUInt32, position) else none

def pushBytes (bytes value : ByteArray) : ByteArray :=
  pushNat bytes value.size ++ value

abbrev Decoder := StateT Nat Option

def Decoder.readNat (bytes : ByteArray) : Decoder Nat := fun position =>
  LeanReach.Cache.Codec.readNat bytes position

def Decoder.readByte (bytes : ByteArray) : Decoder UInt8 := fun position => do
  let value ← bytes[position]?
  return (value, position + 1)

def Decoder.readBytes (bytes : ByteArray) : Decoder ByteArray := fun position => do
  let (size, start) ← readNat bytes position
  let stop := start + size
  if stop ≤ bytes.size then some (bytes.extract start stop, stop) else none

def Decoder.runToEnd {α : Type} (decoder : Decoder α) (bytes : ByteArray) : Option α := do
  let (value, position) ← decoder.run 0
  if position == bytes.size then some value else none

def pushArray (bytes : ByteArray) (values : Array UInt32) : ByteArray :=
  values.foldl pushUInt32 (pushUInt32 bytes values.size.toUInt32)

def packDeltas (values : Array UInt32) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  let mut previous := 0
  for value in values do
    let current := value.toNat
    bytes := pushUInt32 bytes (current - previous).toUInt32
    previous := current
  return bytes

def unpackDeltas (bytes : ByteArray) : Option (Array UInt32) := Id.run do
  let mut values := #[]
  let mut previous := 0
  let mut position := 0
  while position < bytes.size do
    let some (delta, next) := readUInt32 bytes position | return none
    let current := previous + delta.toNat
    if current ≥ 4294967296 then return none
    values := values.push current.toUInt32
    previous := current
    position := next
  return some values

end LeanReach.Cache.Codec
