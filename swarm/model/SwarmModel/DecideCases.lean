import Lean.Data.Json
import SwarmModel.Decide

/-! Random inputs to Decide.lean's lifted functions, with their answers, for ../lua/test/decide_model_spec.lua to
check watchd.keeps, watchd.fate and msgs.wakes against. A `none` is a missing field (the Lua's nil).
`lake env lean --run SwarmModel/DecideCases.lean <n> <seed> <file>` (replay.sh) writes
`{"keeps": [{"o", "bg", "live", "r"}, ..], "fate": [{"a", "t", "x", "terms", "f", "r"}, ..], "wakes": [{"rows", "cold", "r"}, ..]}`. -/

open Lean Swarm.Decide

abbrev G := StateM StdGen

def rnd (n : Nat) : G Nat := modifyGet fun g => randNat g 0 n
def oneOf {α} [Inhabited α] (l : List α) : G α := return l.getD (← rnd (l.length - 1)) default
def opt {α} (x : G α) : G (Option α) := do if (← rnd 2) == 0 then return none else return some (← x)
def coin : G Bool := return (← rnd 1) == 1

/-- an object with the `none` fields left out -/
def obj (l : List (String × Option Json)) : Json := Json.mkObj (l.filterMap fun (k, v) => v.map (k, ·))

def now : Int := 1000000

def row : G ARow := do
  return { ended := ← opt (rnd 5), status := ← oneOf ["idle", "idle", "working", "blocked", "ended", ""],
           hc := ← opt (oneOf ["", "h1", "h2"]), stay := ← opt (oneOf ["", "x"]),
           lastActive := ← opt (return now - (← rnd 300)), ctx := ← opt (oneOf [0, 39999, 40000, 400000]),
           waiter := ← opt (oneOf [0, 7]) }

def rowJson (r : ARow) : Json :=
  obj [("ended", r.ended.map toJson), ("status", some r.status), ("hc", r.hc.map toJson), ("stay", r.stay.map toJson),
       ("last_active", r.lastActive.map toJson), ("ctx_tokens", r.ctx.map toJson), ("waiter", r.waiter.map toJson)]

def verdict : Verdict → Json
  | .keep => Json.null | .unclean => "unclean" | .reuse => "reuse" | .end_ => "end"

def keepsCase : G Json := do
  let o ← opt row
  let bg ← coin
  let live ← opt (do return (← oneOf [[], ["h1"], ["h2"], ["h1", "h2"]]))
  return obj [("o", o.map rowJson), ("bg", some (toJson bg)), ("live", live.map toJson),
              ("r", some (toJson (keepsL o bg live)))]

def fateCase : G Json := do
  -- mostly idle, aged, staying for nothing: else nearly every case is a keep
  let r ← row
  let r := if (← rnd 3) == 0 then r else { r with status := "idle", stay := none, lastActive := some (now - 200) }
  let terms ← coin
  let x ← if terms then opt (do return ({ cwd := ← opt (oneOf ["", "/r"]), status := ← oneOf ["idle", "done", "working"] } : Swarm.Decide.Term))
    else pure none
  let f : Facts := { ours := ← coin, claims := (← rnd 4) == 0, locks := (← rnd 4) == 0, unlanded := (← rnd 3) == 0,
                     job := (← rnd 3) == 0, pool := ← rnd 2, passedOver := ← coin, alive := ← coin }
  return obj [("a", some (rowJson r)), ("t", some (toJson now)),
              ("x", x.map fun x => obj [("cwd", x.cwd.map toJson), ("status", some x.status)]), ("terms", some (toJson terms)),
              ("f", some (obj [("ours", some (toJson f.ours)), ("claims", some (toJson f.claims)), ("locks", some (toJson f.locks)),
                ("unlanded", some (toJson f.unlanded)), ("job", some (toJson f.job)), ("pool", some (toJson f.pool)), ("passed_over", some (toJson f.passedOver)),
                ("alive", some (toJson f.alive))])),
              ("r", some (verdict (fateL r now x terms f)))]

def wakesCase : G Json := do
  let mut rows := []
  for _ in [0:← rnd 4] do
    rows := rows ++ [({ kind := ← oneOf ["dm", "system", "notice", "all"], urgent := ← opt (oneOf [0, 1]) } : MRow)]
  let cold ← coin
  let r := wakesL rows cold
  return obj [("rows", some (Json.arr (rows.map fun m => obj [("kind", some m.kind), ("urgent", m.urgent.map toJson)]).toArray)),
              ("cold", some (toJson cold)),
              ("r", r.map fun (w, u) => obj [("n", some (toJson w.length)), ("urgent", some (toJson u))])]

def main (args : List String) : IO UInt32 := do
  let [n, seed, file] := args | do IO.eprintln "usage: DecideCases.lean <n> <seed> <file>"; return 1
  let k := n.toNat!
  let j := (do
    let ks ← (List.range k).mapM fun _ => keepsCase
    let fs ← (List.range k).mapM fun _ => fateCase
    let ws ← (List.range k).mapM fun _ => wakesCase
    return Json.mkObj [("keeps", Json.arr ks.toArray), ("fate", Json.arr fs.toArray), ("wakes", Json.arr ws.toArray)])
    |>.run' (mkStdGen seed.toNat!)
  IO.FS.writeFile file j.compress
  return 0
