import Lean.Data.Json

/-! json.lua: JSON as Python's json and the Lua CLI's cjson read and write it, on Lean's `Lean.Json`. A decoded
`null` is `Json.null` here where Lua drops it (nil); the getters below treat both alike. Encoding is compact (`compress`),
as cjson's; object keys come out sorted, where cjson's follow the Lua table, so readers parse it (the Herdr mod does). -/

namespace SwarmLean.Json
open Lean (Json JsonNumber)

/-- The value, or none for text that isn't JSON (json.decode's nil). -/
def decode (s : String) : Option Json := (Json.parse s).toOption

/-- Compact JSON text (json.encode). -/
def encode (j : Json) : String := j.compress

/-- Field `k` of an object, none when absent, null, or `j` is not an object. -/
def field (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

/-- A string value. -/
def str? : Json → Option String
  | .str s => some s
  | _ => none

/-- A number as a float. -/
def num? : Json → Option Float
  | .num n => some n.toFloat
  | _ => none

/-- An integral number (Lua's number that `%d` takes). -/
def int? : Json → Option Int
  | .num n => if n.exponent == 0 then some n.mantissa else
      let f := n.toFloat
      if f == f.floor then some f.toInt64.toInt else none
  | _ => none

/-- Lua's `type(x) == "table"`: an object or an array. -/
def isTable : Json → Bool
  | .obj _ | .arr _ => true
  | _ => false

/-- The elements of an array, [] for anything else (ipairs). -/
def items : Json → List Json
  | .arr a => a.toList
  | _ => []

/-- A string field. -/
def fstr (j : Json) (k : String) : Option String := (field j k).bind str?

/-- An integral field. -/
def fint (j : Json) (k : String) : Option Int := (field j k).bind int?

/-- An optional string as JSON (nil is null). -/
def ostr : Option String → Json
  | some s => .str s
  | none => .null

/-- An optional integer as JSON. -/
def oint : Option Int → Json
  | some i => .num (JsonNumber.fromInt i)
  | none => .null

/-- An integer as JSON. -/
def int (i : Int) : Json := .num (JsonNumber.fromInt i)

/-- A float as JSON: an integral one as the integer, as cjson's `%.16g` prints it. -/
def float (f : Float) : Json :=
  if f == f.floor && f.abs < 1e15 then int f.toInt64.toInt else Lean.toJson f

end SwarmLean.Json
