import Claims.Host
import Lean.Data.Json

/-! The machines `hc` knows. -/

namespace Claims
open Lean (Json)

/-- `{name: machine}` from `hc machine ls --json`, [] without hc. -/
def hcMachines {m : Type → Type} [Monad m] (h : Host m) : m (List (String × Json)) := do
  let txt := match ← h.run ["hc", "machine", "ls", "--json"] with
    | some (c, o) => if c == 0 then o else "{}"
    | none => "{}"
  let ms := match (Json.parse txt).toOption.bind (·.getObjVal? "machines" |>.toOption) with
    | some (.arr a) => a.toList
    | _ => []
  return (ms.filterMap fun x => (x.getObjVal? "name" |>.toOption.bind fun | .str s => some s | _ => none).map (·, x)).reverse

/-- A machine's string field of `hcMachines`. -/
def machineStr (x : Json) (k : String) : Option String :=
  match x.getObjVal? k with | .ok (.str s) => some s | _ => none

end Claims
