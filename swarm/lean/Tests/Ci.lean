import SwarmLean.Lib.Ci

/-! ci_spec.lua's asserts on ci.lua's pure functions. -/

open SwarmLean Ci Lean

#guard ts "1970-01-02T00:00:01Z" == 86401 && ts "2000-03-01T00:00:00Z" == 951868800

/-- A rollup entry. -/
def chk (fields : List (String × String)) : Json := Json.mkObj (fields.map fun (k, v) => (k, Json.str v))

#guard verdict (some (Json.arr #[])) == "pending" && verdict none == "pending"
#guard verdict (some (.arr #[chk [("status", "COMPLETED"), ("conclusion", "SUCCESS")], chk [("status", "COMPLETED"), ("conclusion", "SKIPPED")]])) == "green"
#guard verdict (some (.arr #[chk [("status", "COMPLETED"), ("conclusion", "FAILURE")], chk [("status", "IN_PROGRESS"), ("conclusion", "")]])) == "pending"
#guard verdict (some (.arr #[chk [("status", "COMPLETED"), ("conclusion", "FAILURE")], chk [("__typename", "StatusContext"), ("state", "SUCCESS")]])) == "red"
#guard verdict (some (.arr #[chk [("__typename", "StatusContext"), ("state", "PENDING")]])) == "pending"
#guard prAct "MERGED" "pending" false true == some "done" && prAct "OPEN" "green" true false == some "wake"
#guard prAct "OPEN" "green" false false == none && prAct "OPEN" "pending" true false == none && prAct "OPEN" "red" true true == none
