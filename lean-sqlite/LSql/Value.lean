/-! SQL values: sqlite's five storage classes. -/
namespace LSql

/-- A value of one of sqlite's storage classes (datatype3.html §2). -/
inductive Value where
  | null
  | int (i : Int64)
  | real (f : Float)
  | text (s : String)
  | blob (b : ByteArray)
  deriving Inhabited

/-- sqlite's storage class order for comparisons: NULL < INTEGER/REAL < TEXT < BLOB (datatype3.html §4.1). -/
inductive StorageClass where
  | null | numeric | text | blob
  deriving DecidableEq, Repr, Ord

namespace Value

def storageClass : Value → StorageClass
  | null => .null
  | int _ | real _ => .numeric
  | text _ => .text
  | blob _ => .blob

/-- What `typeof()` returns. -/
def typeName : Value → String
  | null => "null"
  | int _ => "integer"
  | real _ => "real"
  | text _ => "text"
  | blob _ => "blob"

def isNull : Value → Bool
  | null => true
  | _ => false

end Value
end LSql
