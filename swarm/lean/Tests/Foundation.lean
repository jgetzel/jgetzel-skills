import SwarmLean.Util
import SwarmLean.Lib.Json

/-! foundation_spec.lua's asserts on util.lua and json.lua (its re asserts are Tests/Re.lean's, its proc asserts
Tests/Spec/Foundation.lean's: they run processes). util.ago(nil) and util.split with a separator have no Lean form
(Lean's `ago` takes a time, and its callers split with `String.splitOn`). -/

namespace SwarmLean.Tests.Foundation
open SwarmLean

-- util
#guard dur "90s" == some 90 && dur "30m" == some 1800 && dur "2h" == some 7200 && dur "5" == some 5
#guard dur "2d" == none
#guard ago 10000 (10000 - 3725) == "1h02m" && ago 10000 (10000 - 125) == "2m"
#guard d 1000000000000000 == "1000000000000000"
#guard cut "héllo" 2 == "hé"
#guard shquote "a b" == "'a b'" && shquote "it's" == "'it'\"'\"'s'" && shquote "" == "''"
#guard shjoin ["make", "-j4", "x y"] == "make -j4 'x y'"
#guard words "  a  b " == ["a", "b"]
#guard (splitlines "a\nb\n").length == 2 && (splitlines "").length == 0
#guard basename "/x/wt" == "wt" && basename "/x/" == "" && dirname "/x/y" == "/x" && joinPath (joinPath "/a" "b") "c" == "/a/b/c"

-- json
/-- foundation_spec's document. -/
def j : Lean.Json := (Json.decode "{\"a\":null,\"b\":[],\"c\":[1,null],\"d\":\"x/y\"}").getD .null

#guard Json.field j "a" == none && (Json.items ((Json.field j "b").getD .null)).length == 0 &&
  (Json.items ((Json.field j "c").getD .null)).head? == some (Json.int 1)
#guard Json.encode ((Json.field j "b").getD .null) == "[]" && Json.encode (.arr #[]) == "[]" &&
  Json.encode (Lean.Json.mkObj []) == "{}"
#guard Json.encode (Json.float 9007199254740992) == "9007199254740992" && Json.encode (Json.float 4.85) == "4.85" &&
  Json.encode (.str "x/y") == "\"x/y\""
#guard Json.decode "{nope" == none

end SwarmLean.Tests.Foundation
