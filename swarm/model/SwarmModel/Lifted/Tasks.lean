import LuaLean.Shallow

/-! tasks.lua lifted by `lua-lean lift`: each function's parsed body, its shallow form, and the proof
that the two are the same. GENERATED: do not edit. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Swarm.Lifted.Tasks
open Lua


def chunk_body : Block :=
  [(.loc ["util", "db"] [(.call (.var "require") [(.str "swarm.util".toList)]), (.call (.var "require") [(.str "swarm.db".toList)])]), (.loc ["agents", "hook"] [(.call (.var "require") [(.str "swarm.agents".toList)]), (.call (.var "require") [(.str "swarm.hook".toList)])]), (.loc ["unistd"] [(.call (.var "require") [(.str "posix.unistd".toList)])]), (.loc ["M"] [(.table [])]), (.assign [(.index (.var "M") (.str "LEASE".toList))] [(.num (.int 7200))]), (.assign [(.index (.var "M") (.str "RED_TASK".toList))] [(.str "main red: ".toList)]), (.assign [(.index (.var "M") (.str "TASK_KINDS".toList))] [(.table [(.pos (.str "task-add".toList)), (.pos (.str "claim".toList)), (.pos (.str "spawn".toList)), (.pos (.str "done".toList)), (.pos (.str "block".toList)), (.pos (.str "unblock".toList)), (.pos (.str "release".toList)), (.pos (.str "drop".toList))])]), (.locfn "py" ["x"] false 
  [(.ite (.or (.or (.or (.bin .eq (.var "x") .nil) (.bin .eq (.var "x") (.num (.int 0)))) (.bin .eq (.var "x") (.str "".toList))) (.bin .eq (.var "x") .fls)) 
  [(.ret [.nil])] 
  []), (.ret [(.var "x")])]), (.locfn "d" ["n"] false 
  [(.ret [(.call (.index (.var "util") (.str "d".toList)) [(.var "n")])])]), (.assign [(.index (.var "M") (.str "event_task".toList))] [(.func ["e"] false 
  [(.loc ["s"] [(.or (.index (.var "e") (.str "data".toList)) (.str "".toList))]), (.loc ["id", "rest"] [(.method (.var "s") "match" [(.str "^#(%d+)(.*)$".toList)])]), (.ite (.un .not (.var "id")) 
  [(.assign [(.var "id"), (.var "rest")] [(.method (.var "s") "match" [(.str "^auto #(%d+)(.*)$".toList)])])] 
  []), (.ite (.and (.var "id") (.paren (.or (.bin .eq (.var "rest") (.str "".toList)) (.bin .eq (.method (.var "rest") "sub" [(.num (.int 1)), (.num (.int 1))]) (.str " ".toList))))) 
  [(.ret [(.call (.var "tonumber") [(.var "id")])])] 
  []), (.ret [.nil])])]), (.assign [(.index (.var "M") (.str "task_timing".toList))] [(.func ["r", "evs"] false 
  [(.locfn "ts" ["k", "agg"] false 
  [(.loc ["v"] []), (.forin ["_", "e"] [(.call (.var "ipairs") [(.var "evs")])] 
  [(.loc ["kind"] [(.or (.and (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "spawn".toList)) (.str "claim".toList)) (.index (.var "e") (.str "kind".toList)))]), (.ite (.bin .eq (.var "kind") (.var "k")) 
  [(.assign [(.var "v")] [(.or (.and (.var "v") (.call (.var "agg") [(.var "v"), (.index (.var "e") (.str "ts".toList))])) (.index (.var "e") (.str "ts".toList)))])] 
  [])]), (.ret [(.var "v")])]), (.loc ["claims", "holders", "seen", "releases"] [(.num (.int 0)), (.table []), (.table []), (.num (.int 0))]), (.forin ["_", "e"] [(.call (.var "ipairs") [(.var "evs")])] 
  [(.ite (.or (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "claim".toList)) (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "spawn".toList))) 
  [(.assign [(.var "claims")] [(.bin .add (.var "claims") (.num (.int 1)))]), (.ite (.un .not (.index (.var "seen") (.index (.var "e") (.str "agent".toList)))) 
  [(.assign [(.index (.var "seen") (.index (.var "e") (.str "agent".toList)))] [.tru]), (.assign [(.index (.var "holders") (.bin .add (.un .len (.var "holders")) (.num (.int 1))))] [(.index (.var "e") (.str "agent".toList))])] 
  [])] 
  [(.ite (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "release".toList)) 
  [(.assign [(.var "releases")] [(.bin .add (.var "releases") (.num (.int 1)))])] 
  [])])]), (.loc ["created"] [(.or (.call (.var "py") [(.index (.var "r") (.str "created_at".toList))]) (.call (.var "ts") [(.str "task-add".toList), (.index (.var "math") (.str "min".toList))]))]), (.loc ["first"] [(.or (.call (.var "py") [(.index (.var "r") (.str "first_claimed_at".toList))]) (.call (.var "ts") [(.str "claim".toList), (.index (.var "math") (.str "min".toList))]))]), (.loc ["done"] [(.or (.call (.var "py") [(.index (.var "r") (.str "done_at".toList))]) (.paren (.or (.and (.bin .eq (.index (.var "r") (.str "state".toList)) (.str "done".toList)) (.call (.var "ts") [(.str "done".toList), (.index (.var "math") (.str "max".toList))])) .nil)))]), (.loc ["dropped"] [(.or (.call (.var "py") [(.index (.var "r") (.str "dropped_at".toList))]) (.paren (.or (.and (.bin .eq (.index (.var "r") (.str "state".toList)) (.str "dropped".toList)) (.call (.var "ts") [(.str "drop".toList), (.index (.var "math") (.str "max".toList))])) .nil)))]), (.loc ["stop"] [(.or (.or (.call (.var "py") [(.var "done")]) (.call (.var "py") [(.var "dropped")])) (.call (.index (.var "util") (.str "now".toList)) []))]), (.loc ["blocked", "start"] [(.num (.int 0)), .nil]), (.forin ["_", "e"] [(.call (.var "ipairs") [(.var "evs")])] 
  [(.ite (.and (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "block".toList)) (.bin .eq (.var "start") .nil)) 
  [(.assign [(.var "start")] [(.index (.var "e") (.str "ts".toList))])] 
  [(.ite (.and (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "unblock".toList)) (.bin .ne (.var "start") .nil)) 
  [(.assign [(.var "blocked"), (.var "start")] [(.bin .sub (.bin .add (.var "blocked") (.index (.var "e") (.str "ts".toList))) (.var "start")), .nil])] 
  [])])]), (.ite (.and (.bin .ne (.var "start") .nil) (.bin .eq (.index (.var "r") (.str "state".toList)) (.str "blocked".toList))) 
  [(.assign [(.var "blocked")] [(.bin .sub (.bin .add (.var "blocked") (.var "stop")) (.var "start"))])] 
  []), (.locfn "span" ["a", "b"] false 
  [(.ret [(.or (.and (.and (.bin .ne (.var "a") .nil) (.bin .ne (.var "b") .nil)) (.bin .sub (.var "b") (.var "a"))) .nil)])]), (.ret [(.table [(.named "created_at" (.var "created")), (.named "first_claimed_at" (.var "first")), (.named "done_at" (.var "done")), (.named "dropped_at" (.var "dropped")), (.named "queue_wait_s" (.call (.var "span") [(.var "created"), (.var "first")])), (.named "work_s" (.call (.var "span") [(.var "first"), (.var "done")])), (.named "total_s" (.call (.var "span") [(.var "created"), (.var "done")])), (.named "blocked_s" (.var "blocked")), (.named "claims" (.var "claims")), (.named "releases" (.var "releases")), (.named "holders" (.var "holders")), (.named "claim_ctx" (.index (.var "r") (.str "claim_ctx".toList))), (.named "done_ctx" (.index (.var "r") (.str "done_ctx".toList))), (.named "pr" (.index (.var "r") (.str "pr".toList))), (.named "merged_at" (.index (.var "r") (.str "merged_at".toList))), (.named "ci_conclusion" (.index (.var "r") (.str "ci_conclusion".toList))), (.named "merge_to_green_s" (.call (.var "span") [(.index (.var "r") (.str "merged_at".toList)), (.index (.var "r") (.str "ci_green_at".toList))]))])])])]), (.assign [(.index (.var "M") (.str "task_events".toList))] [(.func ["c", "tid"] false 
  [(.loc ["r"] [(.table [])]), (.forin ["_", "e"] [(.call (.var "ipairs") [(.method (.var "c") "all" [(.bin .concat (.str "select ts,agent,kind,data from event where kind in ('".toList) (.bin .concat (.call (.index (.var "table") (.str "concat".toList)) [(.index (.var "M") (.str "TASK_KINDS".toList)), (.str "','".toList)]) (.str "') order by id".toList)))])])] 
  [(.ite (.bin .eq (.call (.index (.var "M") (.str "event_task".toList)) [(.var "e")]) (.var "tid")) 
  [(.assign [(.index (.var "r") (.bin .add (.un .len (.var "r")) (.num (.int 1))))] [(.var "e")])] 
  [])]), (.ret [(.var "r")])])]), (.assign [(.index (.var "M") (.str "deps_of".toList))] [(.func ["r"] false 
  [(.loc ["r2"] [(.table [])]), (.forin ["x"] [(.method (.paren (.or (.index (.var "r") (.str "deps".toList)) (.str "".toList))) "gmatch" [(.str "[^,]+".toList)])] 
  [(.assign [(.index (.var "r2") (.bin .add (.un .len (.var "r2")) (.num (.int 1))))] [(.call (.var "tonumber") [(.var "x")])])]), (.ret [(.var "r2")])])]), (.assign [(.index (.var "M") (.str "undone".toList))] [(.func ["c", "r"] false 
  [(.loc ["deps", "out"] [(.call (.index (.var "M") (.str "deps_of".toList)) [(.var "r")]), (.table [])]), (.ite (.bin .eq (.un .len (.var "deps")) (.num (.int 0))) 
  [(.ret [(.var "out")])] 
  []), (.loc ["q"] [(.table [])]), (.fornum "i" (.num (.int 1)) (.un .len (.var "deps")) none 
  [(.assign [(.index (.var "q") (.var "i"))] [(.str "?".toList)])]), (.loc ["st"] [(.table [])]), (.forin ["_", "x"] [(.call (.var "ipairs") [(.method (.var "c") "all" [(.bin .concat (.str "select * from task where id in (".toList) (.bin .concat (.call (.index (.var "table") (.str "concat".toList)) [(.var "q"), (.str ",".toList)]) (.str ") and state!='done'".toList))), (.call (.var "unpack") [(.var "deps")])])])] 
  [(.assign [(.index (.var "st") (.index (.var "x") (.str "id".toList)))] [(.var "x")])]), (.forin ["_", "i"] [(.call (.var "ipairs") [(.var "deps")])] 
  [(.ite (.index (.var "st") (.var "i")) 
  [(.assign [(.index (.var "out") (.bin .add (.un .len (.var "out")) (.num (.int 1))))] [(.index (.var "st") (.var "i"))])] 
  [])]), (.ret [(.var "out")])])]), (.assign [(.index (.var "M") (.str "waiters".toList))] [(.func ["c", "tid"] false 
  [(.ret [(.method (.var "c") "all" [(.str "select * from task where state='open' and ','||deps||',' like ?".toList), (.bin .concat (.str "%,".toList) (.bin .concat (.call (.var "d") [(.var "tid")]) (.str ",%".toList)))])])])]), (.assign [(.index (.var "M") (.str "dep_path".toList))] [(.func ["c", "start", "target"] false 
  [(.loc ["seen", "stack"] [(.table []), (.table [(.pos (.table [(.pos (.var "start"))]))])]), (.while (.bin .gt (.un .len (.var "stack")) (.num (.int 0))) 
  [(.loc ["path"] [(.call (.index (.var "table") (.str "remove".toList)) [(.var "stack")])]), (.loc ["last"] [(.index (.var "path") (.un .len (.var "path")))]), (.ite (.bin .eq (.var "last") (.var "target")) 
  [(.ret [(.var "path")])] 
  []), (.ite (.un .not (.index (.var "seen") (.var "last"))) 
  [(.assign [(.index (.var "seen") (.var "last"))] [.tru]), (.loc ["r"] [(.method (.var "c") "one" [(.str "select * from task where id=?".toList), (.var "last")])]), (.loc ["deps"] [(.or (.and (.var "r") (.call (.index (.var "M") (.str "deps_of".toList)) [(.var "r")])) (.table []))]), (.fornum "i" (.un .len (.var "deps")) (.num (.int 1)) (some (.num (.int (-1)))) 
  [(.loc ["p"] [(.table [(.pos (.call (.var "unpack") [(.var "path")]))])]), (.assign [(.index (.var "p") (.bin .add (.un .len (.var "p")) (.num (.int 1))))] [(.index (.var "deps") (.var "i"))]), (.assign [(.index (.var "stack") (.bin .add (.un .len (.var "stack")) (.num (.int 1))))] [(.var "p")])])] 
  [])]), (.ret [.nil])])]), (.assign [(.index (.var "M") (.str "pool".toList))] [(.func ["c"] false 
  [(.ret [(.method (.var "c") "all" [(.bin .concat (.str "select * from task t where state='open' and not exists (select 1 from task d where d.state!='done' ".toList) (.str "and ','||t.deps||',' like '%,'||d.id||',%') order by title like ? desc, id".toList)), (.bin .concat (.index (.var "M") (.str "RED_TASK".toList)) (.str "%".toList))])])])]), (.assign [(.index (.var "M") (.str "dep_lines".toList))] [(.func ["c", "r"] false 
  [(.loc ["st"] [(.table [])]), (.forin ["_", "x"] [(.call (.var "ipairs") [(.method (.var "c") "all" [(.str "select id,state from task".toList)])])] 
  [(.assign [(.index (.var "st") (.index (.var "x") (.str "id".toList)))] [(.index (.var "x") (.str "state".toList))])]), (.loc ["deps", "out"] [(.call (.index (.var "M") (.str "deps_of".toList)) [(.var "r")]), (.str "".toList)]), (.ite (.bin .gt (.un .len (.var "deps")) (.num (.int 0))) 
  [(.loc ["p"] [(.table [])]), (.forin ["i", "x"] [(.call (.var "ipairs") [(.var "deps")])] 
  [(.assign [(.index (.var "p") (.var "i"))] [(.bin .concat (.str "#".toList) (.bin .concat (.call (.var "d") [(.var "x")]) (.bin .concat (.str " ".toList) (.paren (.or (.index (.var "st") (.var "x")) (.str "missing".toList))))))])]), (.assign [(.var "out")] [(.bin .concat (.str "\nafter: ".toList) (.call (.index (.var "table") (.str "concat".toList)) [(.var "p"), (.str ", ".toList)]))])] 
  []), (.loc ["w"] [(.or (.and (.bin .ne (.index (.var "r") (.str "state".toList)) (.str "done".toList)) (.call (.index (.var "M") (.str "waiters".toList)) [(.var "c"), (.index (.var "r") (.str "id".toList))])) (.table []))]), (.ite (.bin .gt (.un .len (.var "w")) (.num (.int 0))) 
  [(.loc ["p"] [(.table [])]), (.forin ["i", "x"] [(.call (.var "ipairs") [(.var "w")])] 
  [(.assign [(.index (.var "p") (.var "i"))] [(.bin .concat (.str "#".toList) (.call (.var "d") [(.index (.var "x") (.str "id".toList))]))])]), (.assign [(.var "out")] [(.bin .concat (.var "out") (.bin .concat (.str "\nblocks: ".toList) (.call (.index (.var "table") (.str "concat".toList)) [(.var "p"), (.str ", ".toList)])))])] 
  []), (.ret [(.var "out")])])]), (.locfn "ids" ["rows", "f"] false 
  [(.loc ["p"] [(.table [])]), (.forin ["i", "x"] [(.call (.var "ipairs") [(.var "rows")])] 
  [(.assign [(.index (.var "p") (.var "i"))] [(.or (.and (.var "f") (.call (.var "f") [(.var "x")])) (.bin .concat (.str "#".toList) (.call (.var "d") [(.var "x")])))])]), (.ret [(.call (.index (.var "table") (.str "concat".toList)) [(.var "p"), (.str ", ".toList)])])]), (.locfn "no_task_to_wait_on" ["c", "deps"] false 
  [(.forin ["_", "x"] [(.call (.var "ipairs") [(.var "deps")])] 
  [(.ite (.un .not (.method (.var "c") "one" [(.str "select 1 from task where id=?".toList), (.var "x")])) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "no task #%s to wait on".toList)) "format" [(.call (.var "d") [(.var "x")])])]))] 
  [])])]), (.assign [(.index (.var "M") (.str "set_deps".toList))] [(.func ["c", "id", "deps"] false 
  [(.loc ["ds"] [(.table [])]), (.forin ["i", "x"] [(.call (.var "ipairs") [(.var "deps")])] 
  [(.call (.call (.var "no_task_to_wait_on") [(.var "c"), (.table [(.pos (.var "x"))])])), (.loc ["cyc"] [(.call (.index (.var "M") (.str "dep_path".toList)) [(.var "c"), (.var "x"), (.var "id")])]), (.ite (.var "cyc") 
  [(.call (.call (.index (.var "table") (.str "insert".toList)) [(.var "cyc"), (.num (.int 1)), (.var "id")])), (.loc ["p"] [(.table [])]), (.forin ["j", "y"] [(.call (.var "ipairs") [(.var "cyc")])] 
  [(.assign [(.index (.var "p") (.var "j"))] [(.bin .concat (.str "#".toList) (.call (.var "d") [(.var "y")]))])]), (.call (.call (.index (.var "util") (.str "die".toList)) [(.bin .concat (.str "that would be a cycle: ".toList) (.call (.index (.var "table") (.str "concat".toList)) [(.var "p"), (.str " \xe2\x86\x92 ".toList)]))]))] 
  []), (.assign [(.index (.var "ds") (.var "i"))] [(.call (.var "d") [(.var "x")])])]), (.call (.method (.var "c") "exec" [(.str "update task set deps=? where id=?".toList), (.call (.index (.var "table") (.str "concat".toList)) [(.var "ds"), (.str ",".toList)]), (.var "id")])), (.ret [(.var "ds")])])]), (.locfn "ctx_of" ["c", "n"] false 
  [(.loc ["r"] [(.method (.var "c") "one" [(.str "select ctx_tokens from agent where name=?".toList), (.var "n")])]), (.ret [(.or (.and (.var "r") (.index (.var "r") (.str "ctx_tokens".toList))) (.num (.int 0)))])]), (.locfn "reaped_from" ["c", "n", "id"] false 
  [(.loc ["last"] []), (.forin ["_", "e"] [(.call (.var "ipairs") [(.call (.index (.var "M") (.str "task_events".toList)) [(.var "c"), (.var "id")])])] 
  [(.ite (.or (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "claim".toList)) (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "spawn".toList))) 
  [(.assign [(.var "last")] [(.index (.var "e") (.str "agent".toList))])] 
  [])]), (.ret [(.and (.bin .eq (.var "last") (.var "n")) (.bin .ne (.method (.var "c") "one" [(.str "select 1 from event where kind='reap' and agent=? and data=?".toList), (.var "n"), (.method (.paren (.str "task #%s lease expired".toList)) "format" [(.call (.var "d") [(.var "id")])])]) .nil))])]), (.locfn "owned" ["r"] false 
  [(.ret [(.or (.and (.call (.var "py") [(.index (.var "r") (.str "owner".toList))]) (.paren (.bin .concat (.str ", owned by ".toList) (.index (.var "r") (.str "owner".toList))))) (.str "".toList))])]), (.assign [(.index (.var "M") (.str "cmd_task".toList))] [(.func ["c", "a"] false 
  [(.loc ["n"] [(.call (.index (.var "agents") (.str "me".toList)) [])]), (.loc ["t"] [(.call (.index (.var "util") (.str "now".toList)) [])]), (.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "add".toList)) 
  [(.loc ["deps"] [(.or (.index (.var "a") (.str "after".toList)) (.table []))]), (.loc ["id"] [(.method (.var "c") "tx" [(.func [] false 
  [(.call (.call (.var "no_task_to_wait_on") [(.var "c"), (.var "deps")])), (.loc ["ds"] [(.table [])]), (.forin ["i", "x"] [(.call (.var "ipairs") [(.var "deps")])] 
  [(.assign [(.index (.var "ds") (.var "i"))] [(.call (.var "d") [(.var "x")])])]), (.call (.method (.var "c") "exec" [(.str "insert into task(title,body,created_by,deps,model,effort,base,created_at) values(?,?,?,?,?,?,?,?)".toList), (.index (.var "a") (.str "title".toList)), (.index (.var "a") (.str "body".toList)), (.var "n"), (.call (.var "py") [(.call (.index (.var "table") (.str "concat".toList)) [(.var "ds"), (.str ",".toList)])]), (.index (.var "a") (.str "model".toList)), (.index (.var "a") (.str "effort".toList)), (.index (.var "a") (.str "base".toList)), (.var "t")])), (.loc ["id"] [(.method (.var "c") "last_id" [])]), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "task-add".toList), .nil, (.method (.paren (.str "#%s %s".toList)) "format" [(.call (.var "d") [(.var "id")]), (.index (.var "a") (.str "title".toList))])])), (.ret [(.var "id")])])])]), (.call (.call (.var "print") [(.bin .concat (.str "task #".toList) (.call (.var "d") [(.var "id")]))])), (.ret [])] 
  []), (.loc ["r"] [(.method (.var "c") "one" [(.str "select * from task where id=?".toList), (.index (.var "a") (.str "id".toList))])]), (.ite (.un .not (.var "r")) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.bin .concat (.str "no task #".toList) (.call (.var "d") [(.index (.var "a") (.str "id".toList))]))]))] 
  []), (.loc ["mine"] [(.str " where id=? and owner=? and state='claimed'".toList)]), (.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "claim".toList)) 
  [(.loc ["dep"] [(.index (.call (.index (.var "M") (.str "undone".toList)) [(.var "c"), (.var "r")]) (.num (.int 1)))]), (.ite (.var "dep") 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "#%s waits on #%s (%s%s)".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.call (.var "d") [(.index (.var "dep") (.str "id".toList))]), (.index (.var "dep") (.str "state".toList)), (.or (.and (.call (.var "py") [(.index (.var "dep") (.str "owner".toList))]) (.paren (.bin .concat (.str ", claimed by ".toList) (.index (.var "dep") (.str "owner".toList))))) (.str "".toList))])]))] 
  []), (.call (.call (.index (.var "agents") (.str "touch".toList)) [(.var "c"), (.var "n")])), (.loc ["k"] [(.call (.var "ctx_of") [(.var "c"), (.var "n")])]), (.ite (.and (.bin .ge (.var "k") (.index (.var "hook") (.str "CTX_WARN".toList))) (.un .not (.call (.var "reaped_from") [(.var "c"), (.var "n"), (.index (.var "a") (.str "id".toList))]))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "context ~%dk, too high to take new work: %s".toList)) "format" [(.call (.index (.var "math") (.str "floor".toList)) [(.bin .div (.var "k") (.num (.int 1000)))]), (.call (.index (.var "hook") (.str "ctx_advice".toList)) [(.var "k")])])]))] 
  []), (.loc ["until_"] [(.bin .add (.var "t") (.call (.index (.var "util") (.str "dur".toList)) [(.index (.var "a") (.str "lease".toList))]))]), (.ite (.bin .eq (.method (.var "c") "exec" [(.bin .concat (.str "update task set state='claimed', owner=?, lease_until=?, claim_ctx=?, ".toList) (.bin .concat (.str "first_claimed_at=coalesce(first_claimed_at,?) where id=? and state='open' and not exists ".toList) (.str "(select 1 from task d where d.state!='done' and ','||task.deps||',' like '%,'||d.id||',%')".toList))), (.var "n"), (.var "until_"), (.var "k"), (.var "t"), (.index (.var "a") (.str "id".toList))]) (.num (.int 0))) 
  [(.loc ["r2"] [(.method (.var "c") "one" [(.str "select * from task where id=?".toList), (.index (.var "a") (.str "id".toList))])]), (.loc ["dep2"] [(.and (.bin .eq (.index (.var "r2") (.str "state".toList)) (.str "open".toList)) (.index (.call (.index (.var "M") (.str "undone".toList)) [(.var "c"), (.var "r2")]) (.num (.int 1))))]), (.ite (.var "dep2") 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "#%s waits on #%s (%s)".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.call (.var "d") [(.index (.var "dep2") (.str "id".toList))]), (.index (.var "dep2") (.str "state".toList))])]))] 
  []), (.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is %s%s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "r2") (.str "state".toList)), (.call (.var "owned") [(.var "r2")])])]))] 
  []), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "claim".toList), .nil, (.method (.paren (.str "#%s %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "r") (.str "title".toList))])])), (.call (.call (.var "print") [(.method (.paren (.str "claimed #%s until %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.call (.index (.var "util") (.str "hhmm".toList)) [(.var "until_")])])])), (.loc ["machine"] [(.call (.var "require") [(.str "swarm.machine".toList)])]), (.loc ["avail", "total", "psi"] [(.call (.index (.var "machine") (.str "mem".toList)) [])]), (.ite (.var "avail") 
  [(.call (.call (.var "print") [(.or (.and (.call (.index (.var "machine") (.str "pressure_high".toList)) [(.var "avail"), (.var "total"), (.var "psi")]) (.call (.index (.var "machine") (.str "machine_note".toList)) [(.var "c"), (.var "n")])) (.call (.index (.var "machine") (.str "machine_line".toList)) [(.var "avail"), (.var "total"), (.var "psi")]))]))] 
  []), (.call (.call (.var "print") [(.or (.call (.var "py") [(.index (.var "r") (.str "body".toList))]) (.str "(no body)".toList))]))] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "show".toList)) 
  [(.loc ["tm"] [(.call (.index (.var "M") (.str "task_timing".toList)) [(.var "r"), (.call (.index (.var "M") (.str "task_events".toList)) [(.var "c"), (.index (.var "r") (.str "id".toList))])])]), (.locfn "f" ["k"] false 
  [(.ret [(.or (.and (.bin .ne (.index (.var "tm") (.var "k")) .nil) (.method (.paren (.str "%dm".toList)) "format" [(.call (.index (.var "math") (.str "floor".toList)) [(.bin .div (.index (.var "tm") (.var "k")) (.num (.int 60)))])])) (.str "-".toList))])]), (.loc ["s"] [(.method (.paren (.str "#%s %s %s  %s\ntiming: queue %s, work %s, total %s, blocked %s, claims %d, releases %d, held by %s".toList)) "format" [(.call (.var "d") [(.index (.var "r") (.str "id".toList))]), (.index (.var "r") (.str "state".toList)), (.or (.call (.var "py") [(.index (.var "r") (.str "owner".toList))]) (.str "-".toList)), (.index (.var "r") (.str "title".toList)), (.call (.var "f") [(.str "queue_wait_s".toList)]), (.call (.var "f") [(.str "work_s".toList)]), (.call (.var "f") [(.str "total_s".toList)]), (.call (.var "f") [(.str "blocked_s".toList)]), (.index (.var "tm") (.str "claims".toList)), (.index (.var "tm") (.str "releases".toList)), (.or (.call (.var "py") [(.call (.index (.var "table") (.str "concat".toList)) [(.index (.var "tm") (.str "holders".toList)), (.str ", ".toList)])]) (.str "-".toList))])]), (.ite (.call (.var "py") [(.index (.var "r") (.str "base".toList))]) 
  [(.assign [(.var "s")] [(.bin .concat (.var "s") (.bin .concat (.str "\nbase: ".toList) (.index (.var "r") (.str "base".toList))))])] 
  []), (.ite (.call (.var "py") [(.index (.var "tm") (.str "claim_ctx".toList))]) 
  [(.assign [(.var "s")] [(.bin .concat (.var "s") (.method (.paren (.str ", ctx %dk at claim".toList)) "format" [(.call (.index (.var "math") (.str "floor".toList)) [(.bin .div (.index (.var "tm") (.str "claim_ctx".toList)) (.num (.int 1000)))])]))])] 
  []), (.ite (.call (.var "py") [(.index (.var "tm") (.str "done_ctx".toList))]) 
  [(.assign [(.var "s")] [(.bin .concat (.var "s") (.method (.paren (.str " -> %dk at done".toList)) "format" [(.call (.index (.var "math") (.str "floor".toList)) [(.bin .div (.index (.var "tm") (.str "done_ctx".toList)) (.num (.int 1000)))])]))])] 
  []), (.ite (.call (.var "py") [(.index (.var "tm") (.str "merged_at".toList))]) 
  [(.assign [(.var "s")] [(.bin .concat (.var "s") (.method (.paren (.str "\nPR #%s merged %s, main CI %s".toList)) "format" [(.or (.and (.index (.var "tm") (.str "pr".toList)) (.call (.var "d") [(.index (.var "tm") (.str "pr".toList))])) (.str "None".toList)), (.call (.index (.var "util") (.str "hhmm".toList)) [(.index (.var "tm") (.str "merged_at".toList))]), (.or (.call (.var "py") [(.index (.var "tm") (.str "ci_conclusion".toList))]) (.str "pending".toList))]))]), (.ite (.bin .ne (.index (.var "tm") (.str "merge_to_green_s".toList)) .nil) 
  [(.assign [(.var "s")] [(.bin .concat (.var "s") (.method (.paren (.str ", green %dm after merge".toList)) "format" [(.call (.index (.var "math") (.str "floor".toList)) [(.bin .div (.index (.var "tm") (.str "merge_to_green_s".toList)) (.num (.int 60)))])]))])] 
  [])] 
  []), (.call (.call (.var "print") [(.bin .concat (.var "s") (.bin .concat (.call (.index (.var "M") (.str "dep_lines".toList)) [(.var "c"), (.var "r")]) (.bin .concat (.str "\n".toList) (.bin .concat (.paren (.or (.call (.var "py") [(.index (.var "r") (.str "body".toList))]) (.str "(no body)".toList))) (.paren (.or (.and (.call (.var "py") [(.index (.var "r") (.str "answer".toList))]) (.bin .concat (.str "\nAnswer to the block: ".toList) (.index (.var "r") (.str "answer".toList)))) (.str "".toList)))))))]))] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "after".toList)) 
  [(.call (.method (.var "c") "tx" [(.func [] false 
  [(.loc ["r2"] [(.method (.var "c") "one" [(.str "select * from task where id=?".toList), (.index (.var "a") (.str "id".toList))])]), (.ite (.bin .ne (.index (.var "r2") (.str "state".toList)) (.str "open".toList)) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is %s; only an open task's dependencies can change".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "r2") (.str "state".toList))])]))] 
  []), (.loc ["ds"] [(.call (.index (.var "M") (.str "set_deps".toList)) [(.var "c"), (.index (.var "a") (.str "id".toList)), (.index (.var "a") (.str "deps".toList))])]), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "task-after".toList), .nil, (.method (.paren (.str "#%s after %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.or (.call (.var "py") [(.call (.index (.var "table") (.str "concat".toList)) [(.var "ds"), (.str ",".toList)])]) (.str "-".toList))])]))])])), (.call (.call (.var "print") [(.method (.paren (.str "#%s after %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.or (.call (.var "py") [(.call (.var "ids") [(.index (.var "a") (.str "deps".toList))])]) (.str "nothing".toList))])]))] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "renew".toList)) 
  [(.loc ["until_"] [(.bin .add (.var "t") (.call (.index (.var "util") (.str "dur".toList)) [(.index (.var "a") (.str "lease".toList))]))]), (.ite (.bin .eq (.method (.var "c") "exec" [(.bin .concat (.str "update task set lease_until=?".toList) (.var "mine")), (.var "until_"), (.index (.var "a") (.str "id".toList)), (.var "n")]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is not claimed by you".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.call (.call (.var "print") [(.method (.paren (.str "renewed #%s until %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.call (.index (.var "util") (.str "hhmm".toList)) [(.var "until_")])])]))] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "done".toList)) 
  [(.ite (.bin .eq (.call (.index (.var "util") (.str "strip".toList)) [(.or (.index (.var "a") (.str "evidence".toList)) (.str "".toList))]) (.str "".toList)) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.str "--evidence is empty: give the sha, PR or command output that shows the work is done".toList)]))] 
  []), (.ite (.call (.index (.var "util") (.str "startswith".toList)) [(.or (.index (.var "r") (.str "title".toList)) (.str "".toList)), (.index (.var "M") (.str "RED_TASK".toList))]) 
  [(.ite (.bin .eq (.method (.var "c") "exec" [(.bin .concat (.str "update task set evidence=?".toList) (.var "mine")), (.index (.var "a") (.str "evidence".toList)), (.index (.var "a") (.str "id".toList)), (.var "n")]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is not claimed by you".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.call (.call (.var "print") [(.method (.paren (.str "#%s stays yours until a green run: watchd marks it done then, and you can go idle now.".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])])), (.ret [])] 
  []), (.call (.method (.var "c") "tx" [(.func [] false 
  [(.ite (.bin .eq (.method (.var "c") "exec" [(.bin .concat (.str "update task set state='done', evidence=?, lease_until=null, done_at=?, ".toList) (.bin .concat (.str "done_ctx=(select ctx_tokens from agent where name=?)".toList) (.var "mine"))), (.index (.var "a") (.str "evidence".toList)), (.var "t"), (.var "n"), (.index (.var "a") (.str "id".toList)), (.var "n")]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is not claimed by you".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "done".toList), .nil, (.method (.paren (.str "#%s %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "a") (.str "evidence".toList))])]))])])), (.call (.call (.var "print") [(.bin .concat (.str "done #".toList) (.call (.var "d") [(.index (.var "a") (.str "id".toList))]))])), (.loc ["k", "stay"] [(.call (.index (.var "math") (.str "floor".toList)) [(.bin .div (.call (.var "ctx_of") [(.var "c"), (.var "n")]) (.num (.int 1000)))]), (.call (.index (.var "agents") (.str "stay_of".toList)) [(.var "c"), (.var "n")])]), (.ite (.var "stay") 
  [(.call (.call (.var "print") [(.method (.paren (.str "context ~%dk: you stay for '%s'. `swarm stay --end` when that is over.".toList)) "format" [(.var "k"), (.var "stay")])]))] 
  [(.ite (.and (.bin .lt (.bin .mul (.var "k") (.num (.int 1000))) (.index (.var "agents") (.str "SMALL_CTX".toList))) (.bin .gt (.un .len (.call (.index (.var "M") (.str "pool".toList)) [(.var "c")])) (.num (.int 0)))) 
  [(.call (.call (.var "print") [(.method (.paren (.str "context ~%dk: take the next task (swarm board).".toList)) "format" [(.var "k")])]))] 
  [(.call (.call (.var "print") [(.method (.paren (.str "context ~%dk: go idle. watchd ends you once your work lands; a fresh agent takes new work.".toList)) "format" [(.var "k")])]))])])] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "block".toList)) 
  [(.call (.method (.var "c") "tx" [(.func [] false 
  [(.ite (.bin .eq (.method (.var "c") "exec" [(.str "update task set state='blocked', question=? where id=? and owner=? and state='claimed'".toList), (.index (.var "a") (.str "question".toList)), (.index (.var "a") (.str "id".toList)), (.var "n")]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is not claimed by you".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "block".toList), .nil, (.method (.paren (.str "#%s %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "a") (.str "question".toList))])]))])])), (.call (.call (.var "print") [(.method (.paren (.str "blocked #%s; watchd tells the communicator. It stays yours until `swarm task unblock`.".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "unblock".toList)) 
  [(.ite (.bin .ne (.index (.var "r") (.str "state".toList)) (.str "blocked".toList)) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is not blocked".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.ite (.and (.bin .ne (.var "n") (.index (.var "r") (.str "owner".toList))) (.un .not (.call (.index (.var "agents") (.str "is_comms".toList)) [(.var "c"), (.var "n")]))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "only %s or the communicator can unblock #%s".toList)) "format" [(.call (.var "tostring") [(.index (.var "r") (.str "owner".toList))]), (.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.call (.method (.var "c") "tx" [(.func [] false 
  [(.ite (.bin .eq (.method (.var "c") "exec" [(.str "update task set state='claimed', question=null, answer=coalesce(?, answer), lease_until=? where id=? and owner=? and state='blocked'".toList), (.call (.var "py") [(.index (.var "a") (.str "answer".toList))]), (.bin .add (.var "t") (.index (.var "M") (.str "LEASE".toList))), (.index (.var "a") (.str "id".toList)), (.index (.var "r") (.str "owner".toList))]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s changed under you; `swarm task show %s`".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "unblock".toList), .nil, (.bin .concat (.str "#".toList) (.call (.var "d") [(.index (.var "a") (.str "id".toList))]))])), (.ite (.and (.call (.var "py") [(.index (.var "a") (.str "answer".toList))]) (.bin .ne (.var "n") (.index (.var "r") (.str "owner".toList)))) 
  [(.call (.call (.index (.call (.var "require") [(.str "swarm.msgs".toList)]) (.str "post".toList)) [(.var "c"), (.var "n"), (.index (.var "r") (.str "owner".toList)), (.method (.paren (.str "#%s is unblocked. Answer: %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "a") (.str "answer".toList))])]))] 
  [])])])), (.call (.call (.var "print") [(.method (.paren (.str "unblocked #%s; claimed by %s again".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "r") (.str "owner".toList))])]))] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "release".toList)) 
  [(.call (.method (.var "c") "tx" [(.func [] false 
  [(.ite (.bin .eq (.method (.var "c") "exec" [(.str "update task set state='open', owner=null, lease_until=null where id=? and owner=? and state='claimed'".toList), (.index (.var "a") (.str "id".toList)), (.var "n")]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is not claimed by you".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.ite (.index (.var "a") (.str "after".toList)) 
  [(.call (.call (.index (.var "M") (.str "set_deps".toList)) [(.var "c"), (.index (.var "a") (.str "id".toList)), (.index (.var "a") (.str "after".toList))]))] 
  []), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "release".toList), .nil, (.bin .concat (.str "#".toList) (.call (.var "d") [(.index (.var "a") (.str "id".toList))]))]))])])), (.call (.call (.var "print") [(.method (.paren (.str "released #%s; it is open again%s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.or (.and (.and (.index (.var "a") (.str "after".toList)) (.bin .gt (.un .len (.index (.var "a") (.str "after".toList))) (.num (.int 0)))) (.paren (.bin .concat (.str " after ".toList) (.call (.var "ids") [(.index (.var "a") (.str "after".toList))])))) (.str "".toList))])]))] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "drop".toList)) 
  [(.call (.method (.var "c") "tx" [(.func [] false 
  [(.loc ["r2"] [(.method (.var "c") "one" [(.str "select * from task where id=?".toList), (.index (.var "a") (.str "id".toList))])]), (.ite (.and (.and (.paren (.or (.bin .eq (.index (.var "r2") (.str "state".toList)) (.str "claimed".toList)) (.bin .eq (.index (.var "r2") (.str "state".toList)) (.str "blocked".toList)))) (.bin .ne (.index (.var "r2") (.str "owner".toList)) (.var "n"))) (.un .not (.call (.index (.var "agents") (.str "is_comms".toList)) [(.var "c"), (.var "n")]))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "#%s is %s by %s; only it or the communicator can drop it".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "r2") (.str "state".toList)), (.call (.var "tostring") [(.index (.var "r2") (.str "owner".toList))])])]))] 
  []), (.call (.method (.var "c") "exec" [(.str "update task set state='dropped', owner=null, lease_until=null, dropped_at=? where id=?".toList), (.var "t"), (.index (.var "a") (.str "id".toList))])), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "drop".toList), .nil, (.bin .concat (.str "#".toList) (.call (.var "d") [(.index (.var "a") (.str "id".toList))]))]))])])), (.call (.call (.var "print") [(.bin .concat (.str "dropped #".toList) (.call (.var "d") [(.index (.var "a") (.str "id".toList))]))])), (.forin ["_", "w"] [(.call (.var "ipairs") [(.call (.index (.var "M") (.str "waiters".toList)) [(.var "c"), (.index (.var "a") (.str "id".toList))])])] 
  [(.call (.call (.var "print") [(.method (.paren (.str "#%s waits on #%s: drop it too, or `swarm task after %s \xe2\x80\xa6`".toList)) "format" [(.call (.var "d") [(.index (.var "w") (.str "id".toList))]), (.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.call (.var "d") [(.index (.var "w") (.str "id".toList))])])]))])] 
  [])])])])])])])])])])]), (.assign [(.index (.var "M") (.str "cmd_board".toList))] [(.func ["c", "a"] false 
  [(.loc ["machine"] [(.call (.var "require") [(.str "swarm.machine".toList)])]), (.loc ["avail", "total", "psi"] [(.call (.index (.var "machine") (.str "mem".toList)) [])]), (.ite (.var "avail") 
  [(.call (.call (.var "print") [(.call (.index (.var "machine") (.str "machine_line".toList)) [(.var "avail"), (.var "total"), (.var "psi")])]))] 
  []), (.loc ["role"] [(.table [])]), (.forin ["_", "x"] [(.call (.var "ipairs") [(.method (.var "c") "all" [(.str "select name, role from agent where ended is null and role is not null".toList)])])] 
  [(.assign [(.index (.var "role") (.index (.var "x") (.str "name".toList)))] [(.index (.var "x") (.str "role".toList))])]), (.loc ["rows"] [(.method (.var "c") "all" [(.bin .concat (.str "select * from task ".toList) (.bin .concat (.paren (.or (.and (.index (.var "a") (.str "all".toList)) (.str "".toList)) (.str "where state in ('open','claimed','blocked') ".toList))) (.bin .concat (.str "order by title like '".toList) (.bin .concat (.index (.var "M") (.str "RED_TASK".toList)) (.str "%' and state!='done' desc, id".toList)))))])]), (.call (.call (.var "print") [(.call (.index (.var "agents") (.str "limits_line".toList)) [(.var "c")])])), (.loc ["held"] [(.method (.var "c") "one" [(.str "select v from meta where k='spawn_held'".toList)])]), (.ite (.var "held") 
  [(.call (.call (.var "print") [(.index (.var "held") (.str "v".toList))]))] 
  []), (.forin ["_", "r"] [(.call (.var "ipairs") [(.var "rows")])] 
  [(.loc ["who"] [(.bin .concat (.paren (.or (.call (.var "py") [(.index (.var "r") (.str "owner".toList))]) (.str "-".toList))) (.paren (.or (.and (.index (.var "role") (.index (.var "r") (.str "owner".toList))) (.paren (.bin .concat (.str " (".toList) (.bin .concat (.index (.var "role") (.index (.var "r") (.str "owner".toList))) (.str ")".toList))))) (.str "".toList))))]), (.ite (.bin .eq (.index (.var "r") (.str "state".toList)) (.str "blocked".toList)) 
  [(.call (.call (.var "print") [(.method (.paren (.str "#%s blocked by %s: %s  %s".toList)) "format" [(.call (.var "d") [(.index (.var "r") (.str "id".toList))]), (.var "who"), (.or (.index (.var "r") (.str "question".toList)) (.str "None".toList)), (.index (.var "r") (.str "title".toList))])]))] 
  [(.loc ["lease"] [(.str "".toList)]), (.ite (.bin .eq (.index (.var "r") (.str "state".toList)) (.str "claimed".toList)) 
  [(.loc ["left"] [(.bin .sub (.paren (.or (.index (.var "r") (.str "lease_until".toList)) (.num (.int 0)))) (.call (.index (.var "util") (.str "now".toList)) []))]), (.assign [(.var "lease")] [(.or (.and (.bin .gt (.var "left") (.num (.int 0))) (.method (.paren (.str " lease %dm left".toList)) "format" [(.call (.index (.var "math") (.str "floor".toList)) [(.bin .div (.var "left") (.num (.int 60)))])])) (.str " lease EXPIRED".toList))])] 
  []), (.loc ["u"] [(.call (.index (.var "M") (.str "undone".toList)) [(.var "c"), (.var "r")])]), (.loc ["wait"] [(.or (.and (.bin .gt (.un .len (.var "u")) (.num (.int 0))) (.paren (.bin .concat (.str " after ".toList) (.call (.var "ids") [(.var "u"), (.func ["x"] false 
  [(.ret [(.bin .concat (.str "#".toList) (.bin .concat (.call (.var "d") [(.index (.var "x") (.str "id".toList))]) (.paren (.or (.and (.bin .eq (.index (.var "x") (.str "state".toList)) (.str "dropped".toList)) (.str " (dropped)".toList)) (.str "".toList)))))])])])))) (.str "".toList))]), (.call (.call (.var "print") [(.bin .concat (.method (.paren (.str "#%s %-7s %s%s%s  %s".toList)) "format" [(.call (.var "d") [(.index (.var "r") (.str "id".toList))]), (.index (.var "r") (.str "state".toList)), (.var "who"), (.var "lease"), (.var "wait"), (.index (.var "r") (.str "title".toList))]) (.bin .concat (.paren (.or (.and (.call (.var "py") [(.index (.var "r") (.str "body".toList))]) (.str "  [body: task show]".toList)) (.str "".toList))) (.paren (.or (.and (.call (.var "py") [(.index (.var "r") (.str "evidence".toList))]) (.paren (.bin .concat (.str "  [evidence: ".toList) (.bin .concat (.index (.var "r") (.str "evidence".toList)) (.str "]".toList))))) (.str "".toList)))))]))])]), (.ite (.index (.var "a") (.str "all".toList)) 
  [(.call (.call (.var "print") [(.method (.paren (.str "(%d tasks)".toList)) "format" [(.un .len (.var "rows"))])]))] 
  [(.call (.call (.var "print") [(.method (.paren (.str "(%d shown, %d done)".toList)) "format" [(.un .len (.var "rows")), (.index (.method (.var "c") "one" [(.str "select count(*) n from task where state='done'".toList)]) (.str "n".toList))])]))]), (.forin ["_", "x"] [(.call (.var "ipairs") [(.method (.var "c") "all" [(.str "select name, role, stay from agent where ended is null and stay is not null order by name".toList)])])] 
  [(.call (.call (.var "print") [(.method (.paren (.str "staying: %s%s: %s".toList)) "format" [(.index (.var "x") (.str "name".toList)), (.or (.and (.index (.var "x") (.str "role".toList)) (.paren (.bin .concat (.str " ".toList) (.index (.var "x") (.str "role".toList))))) (.str "".toList)), (.index (.var "x") (.str "stay".toList))])]))])])]), (.assign [(.index (.var "M") (.str "cmd_rules".toList))] [(.func ["c", "a"] false 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "set".toList)) 
  [(.call (.method (.var "c") "exec" [(.str "insert or replace into meta(k,v) values('rules',?)".toList), (.call (.index (.var "table") (.str "concat".toList)) [(.index (.var "a") (.str "text".toList)), (.str " ".toList)])]))] 
  []), (.loc ["r"] [(.method (.var "c") "one" [(.str "select v from meta where k='rules'".toList)])]), (.call (.call (.var "print") [(.or (.and (.var "r") (.paren (.or (.index (.var "r") (.str "v".toList)) (.str "None".toList)))) (.str "(none)".toList))]))])]), (.assign [(.index (.var "M") (.str "reserve".toList))] [(.func ["c", "name", "tid", "model"] false 
  [(.loc ["t"] [(.call (.index (.var "util") (.str "now".toList)) [])]), (.ret [(.method (.var "c") "tx" [(.func [] false 
  [(.call (.call (.index (.var "agents") (.str "reserve".toList)) [(.var "c"), (.var "name"), (.var "model")])), (.loc ["r"] [(.method (.var "c") "one" [(.str "select * from task where id=?".toList), (.var "tid")])]), (.ite (.un .not (.var "r")) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.bin .concat (.str "no task #".toList) (.call (.var "d") [(.var "tid")]))]))] 
  []), (.loc ["u"] [(.call (.index (.var "M") (.str "undone".toList)) [(.var "c"), (.var "r")])]), (.ite (.bin .gt (.un .len (.var "u")) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "#%s waits on %s".toList)) "format" [(.call (.var "d") [(.var "tid")]), (.call (.var "ids") [(.var "u"), (.func ["x"] false 
  [(.ret [(.bin .concat (.str "#".toList) (.call (.var "d") [(.index (.var "x") (.str "id".toList))]))])])])])]))] 
  []), (.ite (.bin .ne (.index (.var "r") (.str "state".toList)) (.str "open".toList)) 
  [(.call (.call (.var "error") [(.table [(.named "exit" (.num (.int 1))), (.named "lost" (.method (.paren (.str "task #%s is %s%s".toList)) "format" [(.call (.var "d") [(.var "tid")]), (.index (.var "r") (.str "state".toList)), (.call (.var "owned") [(.var "r")])]))]), (.num (.int 0))]))] 
  []), (.call (.method (.var "c") "exec" [(.str "update task set state='claimed', owner=?, lease_until=?, first_claimed_at=coalesce(first_claimed_at,?) where id=?".toList), (.var "name"), (.bin .add (.var "t") (.index (.var "M") (.str "LEASE".toList))), (.var "t"), (.var "tid")])), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "name"), (.str "claim".toList), .nil, (.method (.paren (.str "#%s %s".toList)) "format" [(.call (.var "d") [(.var "tid")]), (.index (.var "r") (.str "title".toList))])])), (.ret [(.var "r")])])])])])]), (.assign [(.index (.var "M") (.str "unreserve".toList))] [(.func ["c", "name", "r"] false 
  [(.call (.method (.var "c") "tx" [(.func [] false 
  [(.call (.method (.var "c") "exec" [(.str "update agent set ended=? where name=? and hc is null".toList), (.call (.index (.var "util") (.str "now".toList)) []), (.var "name")])), (.ite (.un .not (.var "r")) 
  [(.ret [])] 
  []), (.call (.method (.var "c") "exec" [(.bin .concat (.str "update task set state='open', owner=null, lease_until=null, first_claimed_at=? where id=? and owner=? ".toList) (.str "and state='claimed'".toList)), (.index (.var "r") (.str "first_claimed_at".toList)), (.index (.var "r") (.str "id".toList)), (.var "name")]))])]))])]), (.ret [(.var "M")])]

def py_body : Block :=
  [(.ite (.or (.or (.or (.bin .eq (.var "x") .nil) (.bin .eq (.var "x") (.num (.int 0)))) (.bin .eq (.var "x") (.str "".toList))) (.bin .eq (.var "x") .fls)) 
  [(.ret [.nil])] 
  []), (.ret [(.var "x")])]

def d_body : Block :=
  [(.ret [(.call (.index (.var "util") (.str "d".toList)) [(.var "n")])])]

def M_event_task_body : Block :=
  [(.loc ["s"] [(.or (.index (.var "e") (.str "data".toList)) (.str "".toList))]), (.loc ["id", "rest"] [(.method (.var "s") "match" [(.str "^#(%d+)(.*)$".toList)])]), (.ite (.un .not (.var "id")) 
  [(.assign [(.var "id"), (.var "rest")] [(.method (.var "s") "match" [(.str "^auto #(%d+)(.*)$".toList)])])] 
  []), (.ite (.and (.var "id") (.paren (.or (.bin .eq (.var "rest") (.str "".toList)) (.bin .eq (.method (.var "rest") "sub" [(.num (.int 1)), (.num (.int 1))]) (.str " ".toList))))) 
  [(.ret [(.call (.var "tonumber") [(.var "id")])])] 
  []), (.ret [.nil])]

def M_task_timing_body : Block :=
  [(.locfn "ts" ["k", "agg"] false 
  [(.loc ["v"] []), (.forin ["_", "e"] [(.call (.var "ipairs") [(.var "evs")])] 
  [(.loc ["kind"] [(.or (.and (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "spawn".toList)) (.str "claim".toList)) (.index (.var "e") (.str "kind".toList)))]), (.ite (.bin .eq (.var "kind") (.var "k")) 
  [(.assign [(.var "v")] [(.or (.and (.var "v") (.call (.var "agg") [(.var "v"), (.index (.var "e") (.str "ts".toList))])) (.index (.var "e") (.str "ts".toList)))])] 
  [])]), (.ret [(.var "v")])]), (.loc ["claims", "holders", "seen", "releases"] [(.num (.int 0)), (.table []), (.table []), (.num (.int 0))]), (.forin ["_", "e"] [(.call (.var "ipairs") [(.var "evs")])] 
  [(.ite (.or (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "claim".toList)) (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "spawn".toList))) 
  [(.assign [(.var "claims")] [(.bin .add (.var "claims") (.num (.int 1)))]), (.ite (.un .not (.index (.var "seen") (.index (.var "e") (.str "agent".toList)))) 
  [(.assign [(.index (.var "seen") (.index (.var "e") (.str "agent".toList)))] [.tru]), (.assign [(.index (.var "holders") (.bin .add (.un .len (.var "holders")) (.num (.int 1))))] [(.index (.var "e") (.str "agent".toList))])] 
  [])] 
  [(.ite (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "release".toList)) 
  [(.assign [(.var "releases")] [(.bin .add (.var "releases") (.num (.int 1)))])] 
  [])])]), (.loc ["created"] [(.or (.call (.var "py") [(.index (.var "r") (.str "created_at".toList))]) (.call (.var "ts") [(.str "task-add".toList), (.index (.var "math") (.str "min".toList))]))]), (.loc ["first"] [(.or (.call (.var "py") [(.index (.var "r") (.str "first_claimed_at".toList))]) (.call (.var "ts") [(.str "claim".toList), (.index (.var "math") (.str "min".toList))]))]), (.loc ["done"] [(.or (.call (.var "py") [(.index (.var "r") (.str "done_at".toList))]) (.paren (.or (.and (.bin .eq (.index (.var "r") (.str "state".toList)) (.str "done".toList)) (.call (.var "ts") [(.str "done".toList), (.index (.var "math") (.str "max".toList))])) .nil)))]), (.loc ["dropped"] [(.or (.call (.var "py") [(.index (.var "r") (.str "dropped_at".toList))]) (.paren (.or (.and (.bin .eq (.index (.var "r") (.str "state".toList)) (.str "dropped".toList)) (.call (.var "ts") [(.str "drop".toList), (.index (.var "math") (.str "max".toList))])) .nil)))]), (.loc ["stop"] [(.or (.or (.call (.var "py") [(.var "done")]) (.call (.var "py") [(.var "dropped")])) (.call (.index (.var "util") (.str "now".toList)) []))]), (.loc ["blocked", "start"] [(.num (.int 0)), .nil]), (.forin ["_", "e"] [(.call (.var "ipairs") [(.var "evs")])] 
  [(.ite (.and (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "block".toList)) (.bin .eq (.var "start") .nil)) 
  [(.assign [(.var "start")] [(.index (.var "e") (.str "ts".toList))])] 
  [(.ite (.and (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "unblock".toList)) (.bin .ne (.var "start") .nil)) 
  [(.assign [(.var "blocked"), (.var "start")] [(.bin .sub (.bin .add (.var "blocked") (.index (.var "e") (.str "ts".toList))) (.var "start")), .nil])] 
  [])])]), (.ite (.and (.bin .ne (.var "start") .nil) (.bin .eq (.index (.var "r") (.str "state".toList)) (.str "blocked".toList))) 
  [(.assign [(.var "blocked")] [(.bin .sub (.bin .add (.var "blocked") (.var "stop")) (.var "start"))])] 
  []), (.locfn "span" ["a", "b"] false 
  [(.ret [(.or (.and (.and (.bin .ne (.var "a") .nil) (.bin .ne (.var "b") .nil)) (.bin .sub (.var "b") (.var "a"))) .nil)])]), (.ret [(.table [(.named "created_at" (.var "created")), (.named "first_claimed_at" (.var "first")), (.named "done_at" (.var "done")), (.named "dropped_at" (.var "dropped")), (.named "queue_wait_s" (.call (.var "span") [(.var "created"), (.var "first")])), (.named "work_s" (.call (.var "span") [(.var "first"), (.var "done")])), (.named "total_s" (.call (.var "span") [(.var "created"), (.var "done")])), (.named "blocked_s" (.var "blocked")), (.named "claims" (.var "claims")), (.named "releases" (.var "releases")), (.named "holders" (.var "holders")), (.named "claim_ctx" (.index (.var "r") (.str "claim_ctx".toList))), (.named "done_ctx" (.index (.var "r") (.str "done_ctx".toList))), (.named "pr" (.index (.var "r") (.str "pr".toList))), (.named "merged_at" (.index (.var "r") (.str "merged_at".toList))), (.named "ci_conclusion" (.index (.var "r") (.str "ci_conclusion".toList))), (.named "merge_to_green_s" (.call (.var "span") [(.index (.var "r") (.str "merged_at".toList)), (.index (.var "r") (.str "ci_green_at".toList))]))])])]

def M_task_events_body : Block :=
  [(.loc ["r"] [(.table [])]), (.forin ["_", "e"] [(.call (.var "ipairs") [(.method (.var "c") "all" [(.bin .concat (.str "select ts,agent,kind,data from event where kind in ('".toList) (.bin .concat (.call (.index (.var "table") (.str "concat".toList)) [(.index (.var "M") (.str "TASK_KINDS".toList)), (.str "','".toList)]) (.str "') order by id".toList)))])])] 
  [(.ite (.bin .eq (.call (.index (.var "M") (.str "event_task".toList)) [(.var "e")]) (.var "tid")) 
  [(.assign [(.index (.var "r") (.bin .add (.un .len (.var "r")) (.num (.int 1))))] [(.var "e")])] 
  [])]), (.ret [(.var "r")])]

def M_deps_of_body : Block :=
  [(.loc ["r2"] [(.table [])]), (.forin ["x"] [(.method (.paren (.or (.index (.var "r") (.str "deps".toList)) (.str "".toList))) "gmatch" [(.str "[^,]+".toList)])] 
  [(.assign [(.index (.var "r2") (.bin .add (.un .len (.var "r2")) (.num (.int 1))))] [(.call (.var "tonumber") [(.var "x")])])]), (.ret [(.var "r2")])]

def M_undone_body : Block :=
  [(.loc ["deps", "out"] [(.call (.index (.var "M") (.str "deps_of".toList)) [(.var "r")]), (.table [])]), (.ite (.bin .eq (.un .len (.var "deps")) (.num (.int 0))) 
  [(.ret [(.var "out")])] 
  []), (.loc ["q"] [(.table [])]), (.fornum "i" (.num (.int 1)) (.un .len (.var "deps")) none 
  [(.assign [(.index (.var "q") (.var "i"))] [(.str "?".toList)])]), (.loc ["st"] [(.table [])]), (.forin ["_", "x"] [(.call (.var "ipairs") [(.method (.var "c") "all" [(.bin .concat (.str "select * from task where id in (".toList) (.bin .concat (.call (.index (.var "table") (.str "concat".toList)) [(.var "q"), (.str ",".toList)]) (.str ") and state!='done'".toList))), (.call (.var "unpack") [(.var "deps")])])])] 
  [(.assign [(.index (.var "st") (.index (.var "x") (.str "id".toList)))] [(.var "x")])]), (.forin ["_", "i"] [(.call (.var "ipairs") [(.var "deps")])] 
  [(.ite (.index (.var "st") (.var "i")) 
  [(.assign [(.index (.var "out") (.bin .add (.un .len (.var "out")) (.num (.int 1))))] [(.index (.var "st") (.var "i"))])] 
  [])]), (.ret [(.var "out")])]

def M_waiters_body : Block :=
  [(.ret [(.method (.var "c") "all" [(.str "select * from task where state='open' and ','||deps||',' like ?".toList), (.bin .concat (.str "%,".toList) (.bin .concat (.call (.var "d") [(.var "tid")]) (.str ",%".toList)))])])]

def M_dep_path_body : Block :=
  [(.loc ["seen", "stack"] [(.table []), (.table [(.pos (.table [(.pos (.var "start"))]))])]), (.while (.bin .gt (.un .len (.var "stack")) (.num (.int 0))) 
  [(.loc ["path"] [(.call (.index (.var "table") (.str "remove".toList)) [(.var "stack")])]), (.loc ["last"] [(.index (.var "path") (.un .len (.var "path")))]), (.ite (.bin .eq (.var "last") (.var "target")) 
  [(.ret [(.var "path")])] 
  []), (.ite (.un .not (.index (.var "seen") (.var "last"))) 
  [(.assign [(.index (.var "seen") (.var "last"))] [.tru]), (.loc ["r"] [(.method (.var "c") "one" [(.str "select * from task where id=?".toList), (.var "last")])]), (.loc ["deps"] [(.or (.and (.var "r") (.call (.index (.var "M") (.str "deps_of".toList)) [(.var "r")])) (.table []))]), (.fornum "i" (.un .len (.var "deps")) (.num (.int 1)) (some (.num (.int (-1)))) 
  [(.loc ["p"] [(.table [(.pos (.call (.var "unpack") [(.var "path")]))])]), (.assign [(.index (.var "p") (.bin .add (.un .len (.var "p")) (.num (.int 1))))] [(.index (.var "deps") (.var "i"))]), (.assign [(.index (.var "stack") (.bin .add (.un .len (.var "stack")) (.num (.int 1))))] [(.var "p")])])] 
  [])]), (.ret [.nil])]

def M_pool_body : Block :=
  [(.ret [(.method (.var "c") "all" [(.bin .concat (.str "select * from task t where state='open' and not exists (select 1 from task d where d.state!='done' ".toList) (.str "and ','||t.deps||',' like '%,'||d.id||',%') order by title like ? desc, id".toList)), (.bin .concat (.index (.var "M") (.str "RED_TASK".toList)) (.str "%".toList))])])]

def M_dep_lines_body : Block :=
  [(.loc ["st"] [(.table [])]), (.forin ["_", "x"] [(.call (.var "ipairs") [(.method (.var "c") "all" [(.str "select id,state from task".toList)])])] 
  [(.assign [(.index (.var "st") (.index (.var "x") (.str "id".toList)))] [(.index (.var "x") (.str "state".toList))])]), (.loc ["deps", "out"] [(.call (.index (.var "M") (.str "deps_of".toList)) [(.var "r")]), (.str "".toList)]), (.ite (.bin .gt (.un .len (.var "deps")) (.num (.int 0))) 
  [(.loc ["p"] [(.table [])]), (.forin ["i", "x"] [(.call (.var "ipairs") [(.var "deps")])] 
  [(.assign [(.index (.var "p") (.var "i"))] [(.bin .concat (.str "#".toList) (.bin .concat (.call (.var "d") [(.var "x")]) (.bin .concat (.str " ".toList) (.paren (.or (.index (.var "st") (.var "x")) (.str "missing".toList))))))])]), (.assign [(.var "out")] [(.bin .concat (.str "\nafter: ".toList) (.call (.index (.var "table") (.str "concat".toList)) [(.var "p"), (.str ", ".toList)]))])] 
  []), (.loc ["w"] [(.or (.and (.bin .ne (.index (.var "r") (.str "state".toList)) (.str "done".toList)) (.call (.index (.var "M") (.str "waiters".toList)) [(.var "c"), (.index (.var "r") (.str "id".toList))])) (.table []))]), (.ite (.bin .gt (.un .len (.var "w")) (.num (.int 0))) 
  [(.loc ["p"] [(.table [])]), (.forin ["i", "x"] [(.call (.var "ipairs") [(.var "w")])] 
  [(.assign [(.index (.var "p") (.var "i"))] [(.bin .concat (.str "#".toList) (.call (.var "d") [(.index (.var "x") (.str "id".toList))]))])]), (.assign [(.var "out")] [(.bin .concat (.var "out") (.bin .concat (.str "\nblocks: ".toList) (.call (.index (.var "table") (.str "concat".toList)) [(.var "p"), (.str ", ".toList)])))])] 
  []), (.ret [(.var "out")])]

def ids_body : Block :=
  [(.loc ["p"] [(.table [])]), (.forin ["i", "x"] [(.call (.var "ipairs") [(.var "rows")])] 
  [(.assign [(.index (.var "p") (.var "i"))] [(.or (.and (.var "f") (.call (.var "f") [(.var "x")])) (.bin .concat (.str "#".toList) (.call (.var "d") [(.var "x")])))])]), (.ret [(.call (.index (.var "table") (.str "concat".toList)) [(.var "p"), (.str ", ".toList)])])]

def no_task_to_wait_on_body : Block :=
  [(.forin ["_", "x"] [(.call (.var "ipairs") [(.var "deps")])] 
  [(.ite (.un .not (.method (.var "c") "one" [(.str "select 1 from task where id=?".toList), (.var "x")])) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "no task #%s to wait on".toList)) "format" [(.call (.var "d") [(.var "x")])])]))] 
  [])])]

def M_set_deps_body : Block :=
  [(.loc ["ds"] [(.table [])]), (.forin ["i", "x"] [(.call (.var "ipairs") [(.var "deps")])] 
  [(.call (.call (.var "no_task_to_wait_on") [(.var "c"), (.table [(.pos (.var "x"))])])), (.loc ["cyc"] [(.call (.index (.var "M") (.str "dep_path".toList)) [(.var "c"), (.var "x"), (.var "id")])]), (.ite (.var "cyc") 
  [(.call (.call (.index (.var "table") (.str "insert".toList)) [(.var "cyc"), (.num (.int 1)), (.var "id")])), (.loc ["p"] [(.table [])]), (.forin ["j", "y"] [(.call (.var "ipairs") [(.var "cyc")])] 
  [(.assign [(.index (.var "p") (.var "j"))] [(.bin .concat (.str "#".toList) (.call (.var "d") [(.var "y")]))])]), (.call (.call (.index (.var "util") (.str "die".toList)) [(.bin .concat (.str "that would be a cycle: ".toList) (.call (.index (.var "table") (.str "concat".toList)) [(.var "p"), (.str " \xe2\x86\x92 ".toList)]))]))] 
  []), (.assign [(.index (.var "ds") (.var "i"))] [(.call (.var "d") [(.var "x")])])]), (.call (.method (.var "c") "exec" [(.str "update task set deps=? where id=?".toList), (.call (.index (.var "table") (.str "concat".toList)) [(.var "ds"), (.str ",".toList)]), (.var "id")])), (.ret [(.var "ds")])]

def ctx_of_body : Block :=
  [(.loc ["r"] [(.method (.var "c") "one" [(.str "select ctx_tokens from agent where name=?".toList), (.var "n")])]), (.ret [(.or (.and (.var "r") (.index (.var "r") (.str "ctx_tokens".toList))) (.num (.int 0)))])]

def reaped_from_body : Block :=
  [(.loc ["last"] []), (.forin ["_", "e"] [(.call (.var "ipairs") [(.call (.index (.var "M") (.str "task_events".toList)) [(.var "c"), (.var "id")])])] 
  [(.ite (.or (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "claim".toList)) (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "spawn".toList))) 
  [(.assign [(.var "last")] [(.index (.var "e") (.str "agent".toList))])] 
  [])]), (.ret [(.and (.bin .eq (.var "last") (.var "n")) (.bin .ne (.method (.var "c") "one" [(.str "select 1 from event where kind='reap' and agent=? and data=?".toList), (.var "n"), (.method (.paren (.str "task #%s lease expired".toList)) "format" [(.call (.var "d") [(.var "id")])])]) .nil))])]

def owned_body : Block :=
  [(.ret [(.or (.and (.call (.var "py") [(.index (.var "r") (.str "owner".toList))]) (.paren (.bin .concat (.str ", owned by ".toList) (.index (.var "r") (.str "owner".toList))))) (.str "".toList))])]

def M_cmd_task_body : Block :=
  [(.loc ["n"] [(.call (.index (.var "agents") (.str "me".toList)) [])]), (.loc ["t"] [(.call (.index (.var "util") (.str "now".toList)) [])]), (.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "add".toList)) 
  [(.loc ["deps"] [(.or (.index (.var "a") (.str "after".toList)) (.table []))]), (.loc ["id"] [(.method (.var "c") "tx" [(.func [] false 
  [(.call (.call (.var "no_task_to_wait_on") [(.var "c"), (.var "deps")])), (.loc ["ds"] [(.table [])]), (.forin ["i", "x"] [(.call (.var "ipairs") [(.var "deps")])] 
  [(.assign [(.index (.var "ds") (.var "i"))] [(.call (.var "d") [(.var "x")])])]), (.call (.method (.var "c") "exec" [(.str "insert into task(title,body,created_by,deps,model,effort,base,created_at) values(?,?,?,?,?,?,?,?)".toList), (.index (.var "a") (.str "title".toList)), (.index (.var "a") (.str "body".toList)), (.var "n"), (.call (.var "py") [(.call (.index (.var "table") (.str "concat".toList)) [(.var "ds"), (.str ",".toList)])]), (.index (.var "a") (.str "model".toList)), (.index (.var "a") (.str "effort".toList)), (.index (.var "a") (.str "base".toList)), (.var "t")])), (.loc ["id"] [(.method (.var "c") "last_id" [])]), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "task-add".toList), .nil, (.method (.paren (.str "#%s %s".toList)) "format" [(.call (.var "d") [(.var "id")]), (.index (.var "a") (.str "title".toList))])])), (.ret [(.var "id")])])])]), (.call (.call (.var "print") [(.bin .concat (.str "task #".toList) (.call (.var "d") [(.var "id")]))])), (.ret [])] 
  []), (.loc ["r"] [(.method (.var "c") "one" [(.str "select * from task where id=?".toList), (.index (.var "a") (.str "id".toList))])]), (.ite (.un .not (.var "r")) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.bin .concat (.str "no task #".toList) (.call (.var "d") [(.index (.var "a") (.str "id".toList))]))]))] 
  []), (.loc ["mine"] [(.str " where id=? and owner=? and state='claimed'".toList)]), (.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "claim".toList)) 
  [(.loc ["dep"] [(.index (.call (.index (.var "M") (.str "undone".toList)) [(.var "c"), (.var "r")]) (.num (.int 1)))]), (.ite (.var "dep") 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "#%s waits on #%s (%s%s)".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.call (.var "d") [(.index (.var "dep") (.str "id".toList))]), (.index (.var "dep") (.str "state".toList)), (.or (.and (.call (.var "py") [(.index (.var "dep") (.str "owner".toList))]) (.paren (.bin .concat (.str ", claimed by ".toList) (.index (.var "dep") (.str "owner".toList))))) (.str "".toList))])]))] 
  []), (.call (.call (.index (.var "agents") (.str "touch".toList)) [(.var "c"), (.var "n")])), (.loc ["k"] [(.call (.var "ctx_of") [(.var "c"), (.var "n")])]), (.ite (.and (.bin .ge (.var "k") (.index (.var "hook") (.str "CTX_WARN".toList))) (.un .not (.call (.var "reaped_from") [(.var "c"), (.var "n"), (.index (.var "a") (.str "id".toList))]))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "context ~%dk, too high to take new work: %s".toList)) "format" [(.call (.index (.var "math") (.str "floor".toList)) [(.bin .div (.var "k") (.num (.int 1000)))]), (.call (.index (.var "hook") (.str "ctx_advice".toList)) [(.var "k")])])]))] 
  []), (.loc ["until_"] [(.bin .add (.var "t") (.call (.index (.var "util") (.str "dur".toList)) [(.index (.var "a") (.str "lease".toList))]))]), (.ite (.bin .eq (.method (.var "c") "exec" [(.bin .concat (.str "update task set state='claimed', owner=?, lease_until=?, claim_ctx=?, ".toList) (.bin .concat (.str "first_claimed_at=coalesce(first_claimed_at,?) where id=? and state='open' and not exists ".toList) (.str "(select 1 from task d where d.state!='done' and ','||task.deps||',' like '%,'||d.id||',%')".toList))), (.var "n"), (.var "until_"), (.var "k"), (.var "t"), (.index (.var "a") (.str "id".toList))]) (.num (.int 0))) 
  [(.loc ["r2"] [(.method (.var "c") "one" [(.str "select * from task where id=?".toList), (.index (.var "a") (.str "id".toList))])]), (.loc ["dep2"] [(.and (.bin .eq (.index (.var "r2") (.str "state".toList)) (.str "open".toList)) (.index (.call (.index (.var "M") (.str "undone".toList)) [(.var "c"), (.var "r2")]) (.num (.int 1))))]), (.ite (.var "dep2") 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "#%s waits on #%s (%s)".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.call (.var "d") [(.index (.var "dep2") (.str "id".toList))]), (.index (.var "dep2") (.str "state".toList))])]))] 
  []), (.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is %s%s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "r2") (.str "state".toList)), (.call (.var "owned") [(.var "r2")])])]))] 
  []), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "claim".toList), .nil, (.method (.paren (.str "#%s %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "r") (.str "title".toList))])])), (.call (.call (.var "print") [(.method (.paren (.str "claimed #%s until %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.call (.index (.var "util") (.str "hhmm".toList)) [(.var "until_")])])])), (.loc ["machine"] [(.call (.var "require") [(.str "swarm.machine".toList)])]), (.loc ["avail", "total", "psi"] [(.call (.index (.var "machine") (.str "mem".toList)) [])]), (.ite (.var "avail") 
  [(.call (.call (.var "print") [(.or (.and (.call (.index (.var "machine") (.str "pressure_high".toList)) [(.var "avail"), (.var "total"), (.var "psi")]) (.call (.index (.var "machine") (.str "machine_note".toList)) [(.var "c"), (.var "n")])) (.call (.index (.var "machine") (.str "machine_line".toList)) [(.var "avail"), (.var "total"), (.var "psi")]))]))] 
  []), (.call (.call (.var "print") [(.or (.call (.var "py") [(.index (.var "r") (.str "body".toList))]) (.str "(no body)".toList))]))] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "show".toList)) 
  [(.loc ["tm"] [(.call (.index (.var "M") (.str "task_timing".toList)) [(.var "r"), (.call (.index (.var "M") (.str "task_events".toList)) [(.var "c"), (.index (.var "r") (.str "id".toList))])])]), (.locfn "f" ["k"] false 
  [(.ret [(.or (.and (.bin .ne (.index (.var "tm") (.var "k")) .nil) (.method (.paren (.str "%dm".toList)) "format" [(.call (.index (.var "math") (.str "floor".toList)) [(.bin .div (.index (.var "tm") (.var "k")) (.num (.int 60)))])])) (.str "-".toList))])]), (.loc ["s"] [(.method (.paren (.str "#%s %s %s  %s\ntiming: queue %s, work %s, total %s, blocked %s, claims %d, releases %d, held by %s".toList)) "format" [(.call (.var "d") [(.index (.var "r") (.str "id".toList))]), (.index (.var "r") (.str "state".toList)), (.or (.call (.var "py") [(.index (.var "r") (.str "owner".toList))]) (.str "-".toList)), (.index (.var "r") (.str "title".toList)), (.call (.var "f") [(.str "queue_wait_s".toList)]), (.call (.var "f") [(.str "work_s".toList)]), (.call (.var "f") [(.str "total_s".toList)]), (.call (.var "f") [(.str "blocked_s".toList)]), (.index (.var "tm") (.str "claims".toList)), (.index (.var "tm") (.str "releases".toList)), (.or (.call (.var "py") [(.call (.index (.var "table") (.str "concat".toList)) [(.index (.var "tm") (.str "holders".toList)), (.str ", ".toList)])]) (.str "-".toList))])]), (.ite (.call (.var "py") [(.index (.var "r") (.str "base".toList))]) 
  [(.assign [(.var "s")] [(.bin .concat (.var "s") (.bin .concat (.str "\nbase: ".toList) (.index (.var "r") (.str "base".toList))))])] 
  []), (.ite (.call (.var "py") [(.index (.var "tm") (.str "claim_ctx".toList))]) 
  [(.assign [(.var "s")] [(.bin .concat (.var "s") (.method (.paren (.str ", ctx %dk at claim".toList)) "format" [(.call (.index (.var "math") (.str "floor".toList)) [(.bin .div (.index (.var "tm") (.str "claim_ctx".toList)) (.num (.int 1000)))])]))])] 
  []), (.ite (.call (.var "py") [(.index (.var "tm") (.str "done_ctx".toList))]) 
  [(.assign [(.var "s")] [(.bin .concat (.var "s") (.method (.paren (.str " -> %dk at done".toList)) "format" [(.call (.index (.var "math") (.str "floor".toList)) [(.bin .div (.index (.var "tm") (.str "done_ctx".toList)) (.num (.int 1000)))])]))])] 
  []), (.ite (.call (.var "py") [(.index (.var "tm") (.str "merged_at".toList))]) 
  [(.assign [(.var "s")] [(.bin .concat (.var "s") (.method (.paren (.str "\nPR #%s merged %s, main CI %s".toList)) "format" [(.or (.and (.index (.var "tm") (.str "pr".toList)) (.call (.var "d") [(.index (.var "tm") (.str "pr".toList))])) (.str "None".toList)), (.call (.index (.var "util") (.str "hhmm".toList)) [(.index (.var "tm") (.str "merged_at".toList))]), (.or (.call (.var "py") [(.index (.var "tm") (.str "ci_conclusion".toList))]) (.str "pending".toList))]))]), (.ite (.bin .ne (.index (.var "tm") (.str "merge_to_green_s".toList)) .nil) 
  [(.assign [(.var "s")] [(.bin .concat (.var "s") (.method (.paren (.str ", green %dm after merge".toList)) "format" [(.call (.index (.var "math") (.str "floor".toList)) [(.bin .div (.index (.var "tm") (.str "merge_to_green_s".toList)) (.num (.int 60)))])]))])] 
  [])] 
  []), (.call (.call (.var "print") [(.bin .concat (.var "s") (.bin .concat (.call (.index (.var "M") (.str "dep_lines".toList)) [(.var "c"), (.var "r")]) (.bin .concat (.str "\n".toList) (.bin .concat (.paren (.or (.call (.var "py") [(.index (.var "r") (.str "body".toList))]) (.str "(no body)".toList))) (.paren (.or (.and (.call (.var "py") [(.index (.var "r") (.str "answer".toList))]) (.bin .concat (.str "\nAnswer to the block: ".toList) (.index (.var "r") (.str "answer".toList)))) (.str "".toList)))))))]))] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "after".toList)) 
  [(.call (.method (.var "c") "tx" [(.func [] false 
  [(.loc ["r2"] [(.method (.var "c") "one" [(.str "select * from task where id=?".toList), (.index (.var "a") (.str "id".toList))])]), (.ite (.bin .ne (.index (.var "r2") (.str "state".toList)) (.str "open".toList)) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is %s; only an open task's dependencies can change".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "r2") (.str "state".toList))])]))] 
  []), (.loc ["ds"] [(.call (.index (.var "M") (.str "set_deps".toList)) [(.var "c"), (.index (.var "a") (.str "id".toList)), (.index (.var "a") (.str "deps".toList))])]), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "task-after".toList), .nil, (.method (.paren (.str "#%s after %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.or (.call (.var "py") [(.call (.index (.var "table") (.str "concat".toList)) [(.var "ds"), (.str ",".toList)])]) (.str "-".toList))])]))])])), (.call (.call (.var "print") [(.method (.paren (.str "#%s after %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.or (.call (.var "py") [(.call (.var "ids") [(.index (.var "a") (.str "deps".toList))])]) (.str "nothing".toList))])]))] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "renew".toList)) 
  [(.loc ["until_"] [(.bin .add (.var "t") (.call (.index (.var "util") (.str "dur".toList)) [(.index (.var "a") (.str "lease".toList))]))]), (.ite (.bin .eq (.method (.var "c") "exec" [(.bin .concat (.str "update task set lease_until=?".toList) (.var "mine")), (.var "until_"), (.index (.var "a") (.str "id".toList)), (.var "n")]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is not claimed by you".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.call (.call (.var "print") [(.method (.paren (.str "renewed #%s until %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.call (.index (.var "util") (.str "hhmm".toList)) [(.var "until_")])])]))] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "done".toList)) 
  [(.ite (.bin .eq (.call (.index (.var "util") (.str "strip".toList)) [(.or (.index (.var "a") (.str "evidence".toList)) (.str "".toList))]) (.str "".toList)) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.str "--evidence is empty: give the sha, PR or command output that shows the work is done".toList)]))] 
  []), (.ite (.call (.index (.var "util") (.str "startswith".toList)) [(.or (.index (.var "r") (.str "title".toList)) (.str "".toList)), (.index (.var "M") (.str "RED_TASK".toList))]) 
  [(.ite (.bin .eq (.method (.var "c") "exec" [(.bin .concat (.str "update task set evidence=?".toList) (.var "mine")), (.index (.var "a") (.str "evidence".toList)), (.index (.var "a") (.str "id".toList)), (.var "n")]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is not claimed by you".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.call (.call (.var "print") [(.method (.paren (.str "#%s stays yours until a green run: watchd marks it done then, and you can go idle now.".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])])), (.ret [])] 
  []), (.call (.method (.var "c") "tx" [(.func [] false 
  [(.ite (.bin .eq (.method (.var "c") "exec" [(.bin .concat (.str "update task set state='done', evidence=?, lease_until=null, done_at=?, ".toList) (.bin .concat (.str "done_ctx=(select ctx_tokens from agent where name=?)".toList) (.var "mine"))), (.index (.var "a") (.str "evidence".toList)), (.var "t"), (.var "n"), (.index (.var "a") (.str "id".toList)), (.var "n")]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is not claimed by you".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "done".toList), .nil, (.method (.paren (.str "#%s %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "a") (.str "evidence".toList))])]))])])), (.call (.call (.var "print") [(.bin .concat (.str "done #".toList) (.call (.var "d") [(.index (.var "a") (.str "id".toList))]))])), (.loc ["k", "stay"] [(.call (.index (.var "math") (.str "floor".toList)) [(.bin .div (.call (.var "ctx_of") [(.var "c"), (.var "n")]) (.num (.int 1000)))]), (.call (.index (.var "agents") (.str "stay_of".toList)) [(.var "c"), (.var "n")])]), (.ite (.var "stay") 
  [(.call (.call (.var "print") [(.method (.paren (.str "context ~%dk: you stay for '%s'. `swarm stay --end` when that is over.".toList)) "format" [(.var "k"), (.var "stay")])]))] 
  [(.ite (.and (.bin .lt (.bin .mul (.var "k") (.num (.int 1000))) (.index (.var "agents") (.str "SMALL_CTX".toList))) (.bin .gt (.un .len (.call (.index (.var "M") (.str "pool".toList)) [(.var "c")])) (.num (.int 0)))) 
  [(.call (.call (.var "print") [(.method (.paren (.str "context ~%dk: take the next task (swarm board).".toList)) "format" [(.var "k")])]))] 
  [(.call (.call (.var "print") [(.method (.paren (.str "context ~%dk: go idle. watchd ends you once your work lands; a fresh agent takes new work.".toList)) "format" [(.var "k")])]))])])] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "block".toList)) 
  [(.call (.method (.var "c") "tx" [(.func [] false 
  [(.ite (.bin .eq (.method (.var "c") "exec" [(.str "update task set state='blocked', question=? where id=? and owner=? and state='claimed'".toList), (.index (.var "a") (.str "question".toList)), (.index (.var "a") (.str "id".toList)), (.var "n")]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is not claimed by you".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "block".toList), .nil, (.method (.paren (.str "#%s %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "a") (.str "question".toList))])]))])])), (.call (.call (.var "print") [(.method (.paren (.str "blocked #%s; watchd tells the communicator. It stays yours until `swarm task unblock`.".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "unblock".toList)) 
  [(.ite (.bin .ne (.index (.var "r") (.str "state".toList)) (.str "blocked".toList)) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is not blocked".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.ite (.and (.bin .ne (.var "n") (.index (.var "r") (.str "owner".toList))) (.un .not (.call (.index (.var "agents") (.str "is_comms".toList)) [(.var "c"), (.var "n")]))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "only %s or the communicator can unblock #%s".toList)) "format" [(.call (.var "tostring") [(.index (.var "r") (.str "owner".toList))]), (.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.call (.method (.var "c") "tx" [(.func [] false 
  [(.ite (.bin .eq (.method (.var "c") "exec" [(.str "update task set state='claimed', question=null, answer=coalesce(?, answer), lease_until=? where id=? and owner=? and state='blocked'".toList), (.call (.var "py") [(.index (.var "a") (.str "answer".toList))]), (.bin .add (.var "t") (.index (.var "M") (.str "LEASE".toList))), (.index (.var "a") (.str "id".toList)), (.index (.var "r") (.str "owner".toList))]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s changed under you; `swarm task show %s`".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "unblock".toList), .nil, (.bin .concat (.str "#".toList) (.call (.var "d") [(.index (.var "a") (.str "id".toList))]))])), (.ite (.and (.call (.var "py") [(.index (.var "a") (.str "answer".toList))]) (.bin .ne (.var "n") (.index (.var "r") (.str "owner".toList)))) 
  [(.call (.call (.index (.call (.var "require") [(.str "swarm.msgs".toList)]) (.str "post".toList)) [(.var "c"), (.var "n"), (.index (.var "r") (.str "owner".toList)), (.method (.paren (.str "#%s is unblocked. Answer: %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "a") (.str "answer".toList))])]))] 
  [])])])), (.call (.call (.var "print") [(.method (.paren (.str "unblocked #%s; claimed by %s again".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "r") (.str "owner".toList))])]))] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "release".toList)) 
  [(.call (.method (.var "c") "tx" [(.func [] false 
  [(.ite (.bin .eq (.method (.var "c") "exec" [(.str "update task set state='open', owner=null, lease_until=null where id=? and owner=? and state='claimed'".toList), (.index (.var "a") (.str "id".toList)), (.var "n")]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is not claimed by you".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.ite (.index (.var "a") (.str "after".toList)) 
  [(.call (.call (.index (.var "M") (.str "set_deps".toList)) [(.var "c"), (.index (.var "a") (.str "id".toList)), (.index (.var "a") (.str "after".toList))]))] 
  []), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "release".toList), .nil, (.bin .concat (.str "#".toList) (.call (.var "d") [(.index (.var "a") (.str "id".toList))]))]))])])), (.call (.call (.var "print") [(.method (.paren (.str "released #%s; it is open again%s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.or (.and (.and (.index (.var "a") (.str "after".toList)) (.bin .gt (.un .len (.index (.var "a") (.str "after".toList))) (.num (.int 0)))) (.paren (.bin .concat (.str " after ".toList) (.call (.var "ids") [(.index (.var "a") (.str "after".toList))])))) (.str "".toList))])]))] 
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "drop".toList)) 
  [(.call (.method (.var "c") "tx" [(.func [] false 
  [(.loc ["r2"] [(.method (.var "c") "one" [(.str "select * from task where id=?".toList), (.index (.var "a") (.str "id".toList))])]), (.ite (.and (.and (.paren (.or (.bin .eq (.index (.var "r2") (.str "state".toList)) (.str "claimed".toList)) (.bin .eq (.index (.var "r2") (.str "state".toList)) (.str "blocked".toList)))) (.bin .ne (.index (.var "r2") (.str "owner".toList)) (.var "n"))) (.un .not (.call (.index (.var "agents") (.str "is_comms".toList)) [(.var "c"), (.var "n")]))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "#%s is %s by %s; only it or the communicator can drop it".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "r2") (.str "state".toList)), (.call (.var "tostring") [(.index (.var "r2") (.str "owner".toList))])])]))] 
  []), (.call (.method (.var "c") "exec" [(.str "update task set state='dropped', owner=null, lease_until=null, dropped_at=? where id=?".toList), (.var "t"), (.index (.var "a") (.str "id".toList))])), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "drop".toList), .nil, (.bin .concat (.str "#".toList) (.call (.var "d") [(.index (.var "a") (.str "id".toList))]))]))])])), (.call (.call (.var "print") [(.bin .concat (.str "dropped #".toList) (.call (.var "d") [(.index (.var "a") (.str "id".toList))]))])), (.forin ["_", "w"] [(.call (.var "ipairs") [(.call (.index (.var "M") (.str "waiters".toList)) [(.var "c"), (.index (.var "a") (.str "id".toList))])])] 
  [(.call (.call (.var "print") [(.method (.paren (.str "#%s waits on #%s: drop it too, or `swarm task after %s \xe2\x80\xa6`".toList)) "format" [(.call (.var "d") [(.index (.var "w") (.str "id".toList))]), (.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.call (.var "d") [(.index (.var "w") (.str "id".toList))])])]))])] 
  [])])])])])])])])])]

def M_cmd_board_body : Block :=
  [(.loc ["machine"] [(.call (.var "require") [(.str "swarm.machine".toList)])]), (.loc ["avail", "total", "psi"] [(.call (.index (.var "machine") (.str "mem".toList)) [])]), (.ite (.var "avail") 
  [(.call (.call (.var "print") [(.call (.index (.var "machine") (.str "machine_line".toList)) [(.var "avail"), (.var "total"), (.var "psi")])]))] 
  []), (.loc ["role"] [(.table [])]), (.forin ["_", "x"] [(.call (.var "ipairs") [(.method (.var "c") "all" [(.str "select name, role from agent where ended is null and role is not null".toList)])])] 
  [(.assign [(.index (.var "role") (.index (.var "x") (.str "name".toList)))] [(.index (.var "x") (.str "role".toList))])]), (.loc ["rows"] [(.method (.var "c") "all" [(.bin .concat (.str "select * from task ".toList) (.bin .concat (.paren (.or (.and (.index (.var "a") (.str "all".toList)) (.str "".toList)) (.str "where state in ('open','claimed','blocked') ".toList))) (.bin .concat (.str "order by title like '".toList) (.bin .concat (.index (.var "M") (.str "RED_TASK".toList)) (.str "%' and state!='done' desc, id".toList)))))])]), (.call (.call (.var "print") [(.call (.index (.var "agents") (.str "limits_line".toList)) [(.var "c")])])), (.loc ["held"] [(.method (.var "c") "one" [(.str "select v from meta where k='spawn_held'".toList)])]), (.ite (.var "held") 
  [(.call (.call (.var "print") [(.index (.var "held") (.str "v".toList))]))] 
  []), (.forin ["_", "r"] [(.call (.var "ipairs") [(.var "rows")])] 
  [(.loc ["who"] [(.bin .concat (.paren (.or (.call (.var "py") [(.index (.var "r") (.str "owner".toList))]) (.str "-".toList))) (.paren (.or (.and (.index (.var "role") (.index (.var "r") (.str "owner".toList))) (.paren (.bin .concat (.str " (".toList) (.bin .concat (.index (.var "role") (.index (.var "r") (.str "owner".toList))) (.str ")".toList))))) (.str "".toList))))]), (.ite (.bin .eq (.index (.var "r") (.str "state".toList)) (.str "blocked".toList)) 
  [(.call (.call (.var "print") [(.method (.paren (.str "#%s blocked by %s: %s  %s".toList)) "format" [(.call (.var "d") [(.index (.var "r") (.str "id".toList))]), (.var "who"), (.or (.index (.var "r") (.str "question".toList)) (.str "None".toList)), (.index (.var "r") (.str "title".toList))])]))] 
  [(.loc ["lease"] [(.str "".toList)]), (.ite (.bin .eq (.index (.var "r") (.str "state".toList)) (.str "claimed".toList)) 
  [(.loc ["left"] [(.bin .sub (.paren (.or (.index (.var "r") (.str "lease_until".toList)) (.num (.int 0)))) (.call (.index (.var "util") (.str "now".toList)) []))]), (.assign [(.var "lease")] [(.or (.and (.bin .gt (.var "left") (.num (.int 0))) (.method (.paren (.str " lease %dm left".toList)) "format" [(.call (.index (.var "math") (.str "floor".toList)) [(.bin .div (.var "left") (.num (.int 60)))])])) (.str " lease EXPIRED".toList))])] 
  []), (.loc ["u"] [(.call (.index (.var "M") (.str "undone".toList)) [(.var "c"), (.var "r")])]), (.loc ["wait"] [(.or (.and (.bin .gt (.un .len (.var "u")) (.num (.int 0))) (.paren (.bin .concat (.str " after ".toList) (.call (.var "ids") [(.var "u"), (.func ["x"] false 
  [(.ret [(.bin .concat (.str "#".toList) (.bin .concat (.call (.var "d") [(.index (.var "x") (.str "id".toList))]) (.paren (.or (.and (.bin .eq (.index (.var "x") (.str "state".toList)) (.str "dropped".toList)) (.str " (dropped)".toList)) (.str "".toList)))))])])])))) (.str "".toList))]), (.call (.call (.var "print") [(.bin .concat (.method (.paren (.str "#%s %-7s %s%s%s  %s".toList)) "format" [(.call (.var "d") [(.index (.var "r") (.str "id".toList))]), (.index (.var "r") (.str "state".toList)), (.var "who"), (.var "lease"), (.var "wait"), (.index (.var "r") (.str "title".toList))]) (.bin .concat (.paren (.or (.and (.call (.var "py") [(.index (.var "r") (.str "body".toList))]) (.str "  [body: task show]".toList)) (.str "".toList))) (.paren (.or (.and (.call (.var "py") [(.index (.var "r") (.str "evidence".toList))]) (.paren (.bin .concat (.str "  [evidence: ".toList) (.bin .concat (.index (.var "r") (.str "evidence".toList)) (.str "]".toList))))) (.str "".toList)))))]))])]), (.ite (.index (.var "a") (.str "all".toList)) 
  [(.call (.call (.var "print") [(.method (.paren (.str "(%d tasks)".toList)) "format" [(.un .len (.var "rows"))])]))] 
  [(.call (.call (.var "print") [(.method (.paren (.str "(%d shown, %d done)".toList)) "format" [(.un .len (.var "rows")), (.index (.method (.var "c") "one" [(.str "select count(*) n from task where state='done'".toList)]) (.str "n".toList))])]))]), (.forin ["_", "x"] [(.call (.var "ipairs") [(.method (.var "c") "all" [(.str "select name, role, stay from agent where ended is null and stay is not null order by name".toList)])])] 
  [(.call (.call (.var "print") [(.method (.paren (.str "staying: %s%s: %s".toList)) "format" [(.index (.var "x") (.str "name".toList)), (.or (.and (.index (.var "x") (.str "role".toList)) (.paren (.bin .concat (.str " ".toList) (.index (.var "x") (.str "role".toList))))) (.str "".toList)), (.index (.var "x") (.str "stay".toList))])]))])]

def M_cmd_rules_body : Block :=
  [(.ite (.bin .eq (.index (.var "a") (.str "act".toList)) (.str "set".toList)) 
  [(.call (.method (.var "c") "exec" [(.str "insert or replace into meta(k,v) values('rules',?)".toList), (.call (.index (.var "table") (.str "concat".toList)) [(.index (.var "a") (.str "text".toList)), (.str " ".toList)])]))] 
  []), (.loc ["r"] [(.method (.var "c") "one" [(.str "select v from meta where k='rules'".toList)])]), (.call (.call (.var "print") [(.or (.and (.var "r") (.paren (.or (.index (.var "r") (.str "v".toList)) (.str "None".toList)))) (.str "(none)".toList))]))]

def M_reserve_body : Block :=
  [(.loc ["t"] [(.call (.index (.var "util") (.str "now".toList)) [])]), (.ret [(.method (.var "c") "tx" [(.func [] false 
  [(.call (.call (.index (.var "agents") (.str "reserve".toList)) [(.var "c"), (.var "name"), (.var "model")])), (.loc ["r"] [(.method (.var "c") "one" [(.str "select * from task where id=?".toList), (.var "tid")])]), (.ite (.un .not (.var "r")) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.bin .concat (.str "no task #".toList) (.call (.var "d") [(.var "tid")]))]))] 
  []), (.loc ["u"] [(.call (.index (.var "M") (.str "undone".toList)) [(.var "c"), (.var "r")])]), (.ite (.bin .gt (.un .len (.var "u")) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "#%s waits on %s".toList)) "format" [(.call (.var "d") [(.var "tid")]), (.call (.var "ids") [(.var "u"), (.func ["x"] false 
  [(.ret [(.bin .concat (.str "#".toList) (.call (.var "d") [(.index (.var "x") (.str "id".toList))]))])])])])]))] 
  []), (.ite (.bin .ne (.index (.var "r") (.str "state".toList)) (.str "open".toList)) 
  [(.call (.call (.var "error") [(.table [(.named "exit" (.num (.int 1))), (.named "lost" (.method (.paren (.str "task #%s is %s%s".toList)) "format" [(.call (.var "d") [(.var "tid")]), (.index (.var "r") (.str "state".toList)), (.call (.var "owned") [(.var "r")])]))]), (.num (.int 0))]))] 
  []), (.call (.method (.var "c") "exec" [(.str "update task set state='claimed', owner=?, lease_until=?, first_claimed_at=coalesce(first_claimed_at,?) where id=?".toList), (.var "name"), (.bin .add (.var "t") (.index (.var "M") (.str "LEASE".toList))), (.var "t"), (.var "tid")])), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "name"), (.str "claim".toList), .nil, (.method (.paren (.str "#%s %s".toList)) "format" [(.call (.var "d") [(.var "tid")]), (.index (.var "r") (.str "title".toList))])])), (.ret [(.var "r")])])])])]

def M_unreserve_body : Block :=
  [(.call (.method (.var "c") "tx" [(.func [] false 
  [(.call (.method (.var "c") "exec" [(.str "update agent set ended=? where name=? and hc is null".toList), (.call (.index (.var "util") (.str "now".toList)) []), (.var "name")])), (.ite (.un .not (.var "r")) 
  [(.ret [])] 
  []), (.call (.method (.var "c") "exec" [(.bin .concat (.str "update task set state='open', owner=null, lease_until=null, first_claimed_at=? where id=? and owner=? ".toList) (.str "and state='claimed'".toList)), (.index (.var "r") (.str "first_claimed_at".toList)), (.index (.var "r") (.str "id".toList)), (.var "name")]))])]))]

def ts_body : Block :=
  [(.loc ["v"] []), (.forin ["_", "e"] [(.call (.var "ipairs") [(.var "evs")])] 
  [(.loc ["kind"] [(.or (.and (.bin .eq (.index (.var "e") (.str "kind".toList)) (.str "spawn".toList)) (.str "claim".toList)) (.index (.var "e") (.str "kind".toList)))]), (.ite (.bin .eq (.var "kind") (.var "k")) 
  [(.assign [(.var "v")] [(.or (.and (.var "v") (.call (.var "agg") [(.var "v"), (.index (.var "e") (.str "ts".toList))])) (.index (.var "e") (.str "ts".toList)))])] 
  [])]), (.ret [(.var "v")])]

def span_body : Block :=
  [(.ret [(.or (.and (.and (.bin .ne (.var "a") .nil) (.bin .ne (.var "b") .nil)) (.bin .sub (.var "b") (.var "a"))) .nil)])]

def M_cmd_task_fn_body : Block :=
  [(.call (.call (.var "no_task_to_wait_on") [(.var "c"), (.var "deps")])), (.loc ["ds"] [(.table [])]), (.forin ["i", "x"] [(.call (.var "ipairs") [(.var "deps")])] 
  [(.assign [(.index (.var "ds") (.var "i"))] [(.call (.var "d") [(.var "x")])])]), (.call (.method (.var "c") "exec" [(.str "insert into task(title,body,created_by,deps,model,effort,base,created_at) values(?,?,?,?,?,?,?,?)".toList), (.index (.var "a") (.str "title".toList)), (.index (.var "a") (.str "body".toList)), (.var "n"), (.call (.var "py") [(.call (.index (.var "table") (.str "concat".toList)) [(.var "ds"), (.str ",".toList)])]), (.index (.var "a") (.str "model".toList)), (.index (.var "a") (.str "effort".toList)), (.index (.var "a") (.str "base".toList)), (.var "t")])), (.loc ["id"] [(.method (.var "c") "last_id" [])]), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "task-add".toList), .nil, (.method (.paren (.str "#%s %s".toList)) "format" [(.call (.var "d") [(.var "id")]), (.index (.var "a") (.str "title".toList))])])), (.ret [(.var "id")])]

def f_body : Block :=
  [(.ret [(.or (.and (.bin .ne (.index (.var "tm") (.var "k")) .nil) (.method (.paren (.str "%dm".toList)) "format" [(.call (.index (.var "math") (.str "floor".toList)) [(.bin .div (.index (.var "tm") (.var "k")) (.num (.int 60)))])])) (.str "-".toList))])]

def M_cmd_task_fn1_body : Block :=
  [(.loc ["r2"] [(.method (.var "c") "one" [(.str "select * from task where id=?".toList), (.index (.var "a") (.str "id".toList))])]), (.ite (.bin .ne (.index (.var "r2") (.str "state".toList)) (.str "open".toList)) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is %s; only an open task's dependencies can change".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "r2") (.str "state".toList))])]))] 
  []), (.loc ["ds"] [(.call (.index (.var "M") (.str "set_deps".toList)) [(.var "c"), (.index (.var "a") (.str "id".toList)), (.index (.var "a") (.str "deps".toList))])]), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "task-after".toList), .nil, (.method (.paren (.str "#%s after %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.or (.call (.var "py") [(.call (.index (.var "table") (.str "concat".toList)) [(.var "ds"), (.str ",".toList)])]) (.str "-".toList))])]))]

def M_cmd_task_fn2_body : Block :=
  [(.ite (.bin .eq (.method (.var "c") "exec" [(.bin .concat (.str "update task set state='done', evidence=?, lease_until=null, done_at=?, ".toList) (.bin .concat (.str "done_ctx=(select ctx_tokens from agent where name=?)".toList) (.var "mine"))), (.index (.var "a") (.str "evidence".toList)), (.var "t"), (.var "n"), (.index (.var "a") (.str "id".toList)), (.var "n")]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is not claimed by you".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "done".toList), .nil, (.method (.paren (.str "#%s %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "a") (.str "evidence".toList))])]))]

def M_cmd_task_fn3_body : Block :=
  [(.ite (.bin .eq (.method (.var "c") "exec" [(.str "update task set state='blocked', question=? where id=? and owner=? and state='claimed'".toList), (.index (.var "a") (.str "question".toList)), (.index (.var "a") (.str "id".toList)), (.var "n")]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is not claimed by you".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "block".toList), .nil, (.method (.paren (.str "#%s %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "a") (.str "question".toList))])]))]

def M_cmd_task_fn4_body : Block :=
  [(.ite (.bin .eq (.method (.var "c") "exec" [(.str "update task set state='claimed', question=null, answer=coalesce(?, answer), lease_until=? where id=? and owner=? and state='blocked'".toList), (.call (.var "py") [(.index (.var "a") (.str "answer".toList))]), (.bin .add (.var "t") (.index (.var "M") (.str "LEASE".toList))), (.index (.var "a") (.str "id".toList)), (.index (.var "r") (.str "owner".toList))]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s changed under you; `swarm task show %s`".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "unblock".toList), .nil, (.bin .concat (.str "#".toList) (.call (.var "d") [(.index (.var "a") (.str "id".toList))]))])), (.ite (.and (.call (.var "py") [(.index (.var "a") (.str "answer".toList))]) (.bin .ne (.var "n") (.index (.var "r") (.str "owner".toList)))) 
  [(.call (.call (.index (.call (.var "require") [(.str "swarm.msgs".toList)]) (.str "post".toList)) [(.var "c"), (.var "n"), (.index (.var "r") (.str "owner".toList)), (.method (.paren (.str "#%s is unblocked. Answer: %s".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "a") (.str "answer".toList))])]))] 
  [])]

def M_cmd_task_fn5_body : Block :=
  [(.ite (.bin .eq (.method (.var "c") "exec" [(.str "update task set state='open', owner=null, lease_until=null where id=? and owner=? and state='claimed'".toList), (.index (.var "a") (.str "id".toList)), (.var "n")]) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "task #%s is not claimed by you".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))])])]))] 
  []), (.ite (.index (.var "a") (.str "after".toList)) 
  [(.call (.call (.index (.var "M") (.str "set_deps".toList)) [(.var "c"), (.index (.var "a") (.str "id".toList)), (.index (.var "a") (.str "after".toList))]))] 
  []), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "release".toList), .nil, (.bin .concat (.str "#".toList) (.call (.var "d") [(.index (.var "a") (.str "id".toList))]))]))]

def M_cmd_task_fn6_body : Block :=
  [(.loc ["r2"] [(.method (.var "c") "one" [(.str "select * from task where id=?".toList), (.index (.var "a") (.str "id".toList))])]), (.ite (.and (.and (.paren (.or (.bin .eq (.index (.var "r2") (.str "state".toList)) (.str "claimed".toList)) (.bin .eq (.index (.var "r2") (.str "state".toList)) (.str "blocked".toList)))) (.bin .ne (.index (.var "r2") (.str "owner".toList)) (.var "n"))) (.un .not (.call (.index (.var "agents") (.str "is_comms".toList)) [(.var "c"), (.var "n")]))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "#%s is %s by %s; only it or the communicator can drop it".toList)) "format" [(.call (.var "d") [(.index (.var "a") (.str "id".toList))]), (.index (.var "r2") (.str "state".toList)), (.call (.var "tostring") [(.index (.var "r2") (.str "owner".toList))])])]))] 
  []), (.call (.method (.var "c") "exec" [(.str "update task set state='dropped', owner=null, lease_until=null, dropped_at=? where id=?".toList), (.var "t"), (.index (.var "a") (.str "id".toList))])), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "n"), (.str "drop".toList), .nil, (.bin .concat (.str "#".toList) (.call (.var "d") [(.index (.var "a") (.str "id".toList))]))]))]

def M_cmd_board_fn_body : Block :=
  [(.ret [(.bin .concat (.str "#".toList) (.bin .concat (.call (.var "d") [(.index (.var "x") (.str "id".toList))]) (.paren (.or (.and (.bin .eq (.index (.var "x") (.str "state".toList)) (.str "dropped".toList)) (.str " (dropped)".toList)) (.str "".toList)))))])]

def M_reserve_fn_body : Block :=
  [(.call (.call (.index (.var "agents") (.str "reserve".toList)) [(.var "c"), (.var "name"), (.var "model")])), (.loc ["r"] [(.method (.var "c") "one" [(.str "select * from task where id=?".toList), (.var "tid")])]), (.ite (.un .not (.var "r")) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.bin .concat (.str "no task #".toList) (.call (.var "d") [(.var "tid")]))]))] 
  []), (.loc ["u"] [(.call (.index (.var "M") (.str "undone".toList)) [(.var "c"), (.var "r")])]), (.ite (.bin .gt (.un .len (.var "u")) (.num (.int 0))) 
  [(.call (.call (.index (.var "util") (.str "die".toList)) [(.method (.paren (.str "#%s waits on %s".toList)) "format" [(.call (.var "d") [(.var "tid")]), (.call (.var "ids") [(.var "u"), (.func ["x"] false 
  [(.ret [(.bin .concat (.str "#".toList) (.call (.var "d") [(.index (.var "x") (.str "id".toList))]))])])])])]))] 
  []), (.ite (.bin .ne (.index (.var "r") (.str "state".toList)) (.str "open".toList)) 
  [(.call (.call (.var "error") [(.table [(.named "exit" (.num (.int 1))), (.named "lost" (.method (.paren (.str "task #%s is %s%s".toList)) "format" [(.call (.var "d") [(.var "tid")]), (.index (.var "r") (.str "state".toList)), (.call (.var "owned") [(.var "r")])]))]), (.num (.int 0))]))] 
  []), (.call (.method (.var "c") "exec" [(.str "update task set state='claimed', owner=?, lease_until=?, first_claimed_at=coalesce(first_claimed_at,?) where id=?".toList), (.var "name"), (.bin .add (.var "t") (.index (.var "M") (.str "LEASE".toList))), (.var "t"), (.var "tid")])), (.call (.call (.index (.var "db") (.str "log".toList)) [(.var "c"), (.var "name"), (.str "claim".toList), .nil, (.method (.paren (.str "#%s %s".toList)) "format" [(.call (.var "d") [(.var "tid")]), (.index (.var "r") (.str "title".toList))])])), (.ret [(.var "r")])]

def M_unreserve_fn_body : Block :=
  [(.call (.method (.var "c") "exec" [(.str "update agent set ended=? where name=? and hc is null".toList), (.call (.index (.var "util") (.str "now".toList)) []), (.var "name")])), (.ite (.un .not (.var "r")) 
  [(.ret [])] 
  []), (.call (.method (.var "c") "exec" [(.bin .concat (.str "update task set state='open', owner=null, lease_until=null, first_claimed_at=? where id=? and owner=? ".toList) (.str "and state='claimed'".toList)), (.index (.var "r") (.str "first_claimed_at".toList)), (.index (.var "r") (.str "id".toList)), (.var "name")]))]

def M_reserve_fn_fn_body : Block :=
  [(.ret [(.bin .concat (.str "#".toList) (.call (.var "d") [(.index (.var "x") (.str "id".toList))]))])]

def chunk (I : Sem) (env0 : Env) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.letEnd ((S.block (S.qLocal (S.lCons (S.eFirst (S.mCall I (S.eGlob "require") (S.lLast (S.mOne (S.eStr "swarm.util".toList))))) (S.lLast (S.mCall I (S.eGlob "require") (S.lLast (S.mOne (S.eStr "swarm.db".toList)))))) fun n => S.let1 fun c_util => S.let1 fun c_db => S.letEnd
      ((S.qLocal (S.lCons (S.eFirst (S.mCall I (S.eGlob "require") (S.lLast (S.mOne (S.eStr "swarm.agents".toList))))) (S.lLast (S.mCall I (S.eGlob "require") (S.lLast (S.mOne (S.eStr "swarm.hook".toList)))))) fun n => S.let1 fun c_agents => S.let1 fun c_hook => S.letEnd
      ((S.qLocal (S.lLast (S.mCall I (S.eGlob "require") (S.lLast (S.mOne (S.eStr "posix.unistd".toList))))) fun n => S.let1 fun c_unistd => S.letEnd
      ((S.qLocal (S.lLast (S.mOne (S.eTable S.fNil))) fun n => S.let1 fun c_M => S.letEnd
      ((S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "LEASE".toList) S.pNil) (S.lLast (S.mOne (S.eNum (.int 7200))))) (S.gotos [] [])
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "RED_TASK".toList) S.pNil) (S.lLast (S.mOne (S.eStr "main red: ".toList)))) (S.gotos [] [])
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "TASK_KINDS".toList) S.pNil) (S.lLast (S.mOne (S.eTable (S.fPos (S.eStr "task-add".toList) (S.fPos (S.eStr "claim".toList) (S.fPos (S.eStr "spawn".toList) (S.fPos (S.eStr "done".toList) (S.fPos (S.eStr "block".toList) (S.fPos (S.eStr "unblock".toList) (S.fPos (S.eStr "release".toList) (S.fLast (S.mOne (S.eStr "drop".toList)))))))))))))) (S.gotos [] [])
      (S.qLocalFn "py" ["x"] false py_body (("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0) fun c_py =>
      (S.qLocalFn "d" ["n"] false d_body (("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0) fun c_d =>
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "event_task".toList) S.pNil) (S.lLast (S.mOne (S.eFunc ["e"] false M_event_task_body (("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0))))) (S.gotos [] [])
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "task_timing".toList) S.pNil) (S.lLast (S.mOne (S.eFunc ["r", "evs"] false M_task_timing_body (("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0))))) (S.gotos [] [])
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "task_events".toList) S.pNil) (S.lLast (S.mOne (S.eFunc ["c", "tid"] false M_task_events_body (("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0))))) (S.gotos [] [])
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "deps_of".toList) S.pNil) (S.lLast (S.mOne (S.eFunc ["r"] false M_deps_of_body (("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0))))) (S.gotos [] [])
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "undone".toList) S.pNil) (S.lLast (S.mOne (S.eFunc ["c", "r"] false M_undone_body (("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0))))) (S.gotos [] [])
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "waiters".toList) S.pNil) (S.lLast (S.mOne (S.eFunc ["c", "tid"] false M_waiters_body (("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0))))) (S.gotos [] [])
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "dep_path".toList) S.pNil) (S.lLast (S.mOne (S.eFunc ["c", "start", "target"] false M_dep_path_body (("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0))))) (S.gotos [] [])
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "pool".toList) S.pNil) (S.lLast (S.mOne (S.eFunc ["c"] false M_pool_body (("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0))))) (S.gotos [] [])
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "dep_lines".toList) S.pNil) (S.lLast (S.mOne (S.eFunc ["c", "r"] false M_dep_lines_body (("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0))))) (S.gotos [] [])
      (S.qLocalFn "ids" ["rows", "f"] false ids_body (("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0) fun c_ids =>
      (S.qLocalFn "no_task_to_wait_on" ["c", "deps"] false no_task_to_wait_on_body (("ids", c_ids) :: ("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0) fun c_no_task_to_wait_on =>
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "set_deps".toList) S.pNil) (S.lLast (S.mOne (S.eFunc ["c", "id", "deps"] false M_set_deps_body (("no_task_to_wait_on", c_no_task_to_wait_on) :: ("ids", c_ids) :: ("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0))))) (S.gotos [] [])
      (S.qLocalFn "ctx_of" ["c", "n"] false ctx_of_body (("no_task_to_wait_on", c_no_task_to_wait_on) :: ("ids", c_ids) :: ("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0) fun c_ctx_of =>
      (S.qLocalFn "reaped_from" ["c", "n", "id"] false reaped_from_body (("ctx_of", c_ctx_of) :: ("no_task_to_wait_on", c_no_task_to_wait_on) :: ("ids", c_ids) :: ("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0) fun c_reaped_from =>
      (S.qLocalFn "owned" ["r"] false owned_body (("reaped_from", c_reaped_from) :: ("ctx_of", c_ctx_of) :: ("no_task_to_wait_on", c_no_task_to_wait_on) :: ("ids", c_ids) :: ("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0) fun c_owned =>
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "cmd_task".toList) S.pNil) (S.lLast (S.mOne (S.eFunc ["c", "a"] false M_cmd_task_body (("owned", c_owned) :: ("reaped_from", c_reaped_from) :: ("ctx_of", c_ctx_of) :: ("no_task_to_wait_on", c_no_task_to_wait_on) :: ("ids", c_ids) :: ("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0))))) (S.gotos [] [])
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "cmd_board".toList) S.pNil) (S.lLast (S.mOne (S.eFunc ["c", "a"] false M_cmd_board_body (("owned", c_owned) :: ("reaped_from", c_reaped_from) :: ("ctx_of", c_ctx_of) :: ("no_task_to_wait_on", c_no_task_to_wait_on) :: ("ids", c_ids) :: ("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0))))) (S.gotos [] [])
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "cmd_rules".toList) S.pNil) (S.lLast (S.mOne (S.eFunc ["c", "a"] false M_cmd_rules_body (("owned", c_owned) :: ("reaped_from", c_reaped_from) :: ("ctx_of", c_ctx_of) :: ("no_task_to_wait_on", c_no_task_to_wait_on) :: ("ids", c_ids) :: ("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0))))) (S.gotos [] [])
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "reserve".toList) S.pNil) (S.lLast (S.mOne (S.eFunc ["c", "name", "tid", "model"] false M_reserve_body (("owned", c_owned) :: ("reaped_from", c_reaped_from) :: ("ctx_of", c_ctx_of) :: ("no_task_to_wait_on", c_no_task_to_wait_on) :: ("ids", c_ids) :: ("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0))))) (S.gotos [] [])
      (S.qStat (S.sAssign (S.pIndex I (S.eCell c_M) (S.eStr "unreserve".toList) S.pNil) (S.lLast (S.mOne (S.eFunc ["c", "name", "r"] false M_unreserve_body (("owned", c_owned) :: ("reaped_from", c_reaped_from) :: ("ctx_of", c_ctx_of) :: ("no_task_to_wait_on", c_no_task_to_wait_on) :: ("ids", c_ids) :: ("d", c_d) :: ("py", c_py) :: ("M", c_M) :: ("unistd", c_unistd) :: ("hook", c_hook) :: ("agents", c_agents) :: ("db", c_db) :: ("util", c_util) :: env0))))) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lLast (S.mOne (S.eCell c_M)))) (S.gotos [] [])
      S.qEnd)))))))))))))))))))))))))) n)) n)) n)) n))) n)

theorem chunk_ok (I : Sem) (env0 : Env)
    (h_require : env0.lookup "require" = none)
    (h_tonumber : env0.lookup "tonumber" = none)
    (h_ipairs : env0.lookup "ipairs" = none)
    (h_math : env0.lookup "math" = none)
    (h_table : env0.lookup "table" = none)
    (h_unpack : env0.lookup "unpack" = none)
    (h_print : env0.lookup "print" = none)
    (h_tostring : env0.lookup "tostring" = none)
    (h_error : env0.lookup "error" = none) :
    CFn I (chunk I env0) ⟨[], true, chunk_body, env0⟩ :=
  CFn_fn fun args n => CBs_end ((CK_block (CQ_local (CL_cons (CE_call (CM_call (CE_glob h_require) (CL_last (CM_one rfl CE_str)))) (CL_last (CM_call (CE_glob h_require) (CL_last (CM_one rfl CE_str))))) fun n => CBs_let fun c_util => CBs_let fun c_db => CBs_end
      ((CQ_local (CL_cons (CE_call (CM_call (CE_glob h_require) (CL_last (CM_one rfl CE_str)))) (CL_last (CM_call (CE_glob h_require) (CL_last (CM_one rfl CE_str))))) fun n => CBs_let fun c_agents => CBs_let fun c_hook => CBs_end
      ((CQ_local (CL_last (CM_call (CE_glob h_require) (CL_last (CM_one rfl CE_str)))) fun n => CBs_let fun c_unistd => CBs_end
      ((CQ_local (CL_last (CM_one rfl (CE_table CF_nil))) fun n => CBs_let fun c_M => CBs_end
      ((CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl CE_num)))
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl CE_str)))
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_table (CF_pos CE_str (CF_pos CE_str (CF_pos CE_str (CF_pos CE_str (CF_pos CE_str (CF_pos CE_str (CF_pos CE_str (CF_last (CM_one rfl CE_str)))))))))))))
      (CQ_localFn (by rfl) fun c_py =>
      (CQ_localFn (by rfl) fun c_d =>
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_func (by rfl)))))
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_func (by rfl)))))
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_func (by rfl)))))
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_func (by rfl)))))
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_func (by rfl)))))
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_func (by rfl)))))
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_func (by rfl)))))
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_func (by rfl)))))
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_func (by rfl)))))
      (CQ_localFn (by rfl) fun c_ids =>
      (CQ_localFn (by rfl) fun c_no_task_to_wait_on =>
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_func (by rfl)))))
      (CQ_localFn (by rfl) fun c_ctx_of =>
      (CQ_localFn (by rfl) fun c_reaped_from =>
      (CQ_localFn (by rfl) fun c_owned =>
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_func (by rfl)))))
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_func (by rfl)))))
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_func (by rfl)))))
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_func (by rfl)))))
      (CQ_stat (CS_assign (CP_index (CE_cell rfl) CE_str CP_nil) (CL_last (CM_one rfl (CE_func (by rfl)))))
      (CQ_stat (CS_return (CL_last (CM_one rfl (CE_cell rfl))))
      CQ_end rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl)))) rfl rfl rfl))) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl))) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) n)) n)) n)) n))) n)

def py (I : Sem) (env0 : Env) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_x => S.letEnd ((S.block (S.qStat (S.sIf (S.eOr (S.eOr (S.eOr (S.eBin I .eq (S.eCell c_x) S.eNil) (S.eBin I .eq (S.eCell c_x) (S.eNum (.int 0)))) (S.eBin I .eq (S.eCell c_x) (S.eStr "".toList))) (S.eBin I .eq (S.eCell c_x) S.eFalse)) (S.block (S.qStat (S.sReturn (S.lLast (S.mOne S.eNil))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lLast (S.mOne (S.eCell c_x)))) (S.gotos [] [])
      S.qEnd))) n)

theorem py_ok (I : Sem) (env0 : Env) :
    CFn I (py I env0) ⟨["x"], false, py_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_x => CBs_end ((CK_block (CQ_stat (CS_if (CE_or (CE_or (CE_or (CE_bin (CE_cell rfl) CE_nil) (CE_bin (CE_cell rfl) CE_num)) (CE_bin (CE_cell rfl) CE_str)) (CE_bin (CE_cell rfl) CE_false)) (CK_block (CQ_stat (CS_return (CL_last (CM_one rfl CE_nil)))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_stat (CS_return (CL_last (CM_one rfl (CE_cell rfl))))
      CQ_end rfl rfl rfl) rfl rfl rfl)) n)

def d (I : Sem) (env0 : Env) (c_util : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_n => S.letEnd ((S.block (S.qStat (S.sReturn (S.lLast (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "d".toList)) (S.lLast (S.mOne (S.eCell c_n)))))) (S.gotos [] [])
      S.qEnd)) n)

theorem d_ok (I : Sem) (env0 : Env) (c_util : Nat)
    (h_util : env0.lookup "util" = some c_util) :
    CFn I (d I env0 c_util) ⟨["n"], false, d_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_n => CBs_end ((CK_block (CQ_stat (CS_return (CL_last (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_one rfl (CE_cell rfl))))))
      CQ_end rfl rfl rfl)) n)

def M_event_task (I : Sem) (env0 : Env) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_e => S.letEnd ((S.block (S.qLocal (S.lLast (S.mOne (S.eOr (S.eIndex I (S.eCell c_e) (S.eStr "data".toList)) (S.eStr "".toList)))) fun n => S.let1 fun c_s => S.letEnd
      ((S.qLocal (S.lLast (S.mMethod I (S.eCell c_s) "match" (S.lLast (S.mOne (S.eStr "^#(%d+)(.*)$".toList))))) fun n => S.let1 fun c_id => S.let1 fun c_rest => S.letEnd
      ((S.qStat (S.sIf (S.eUn .not (S.eCell c_id)) (S.block (S.qStat (S.sAssign (S.pVar (S.wCell c_id) (S.pVar (S.wCell c_rest) S.pNil)) (S.lLast (S.mMethod I (S.eCell c_s) "match" (S.lLast (S.mOne (S.eStr "^auto #(%d+)(.*)$".toList)))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qStat (S.sIf (S.eAnd (S.eCell c_id) (S.eParen (S.eOr (S.eBin I .eq (S.eCell c_rest) (S.eStr "".toList)) (S.eBin I .eq (S.eFirst (S.mMethod I (S.eCell c_rest) "sub" (S.lCons (S.eNum (.int 1)) (S.lLast (S.mOne (S.eNum (.int 1))))))) (S.eStr " ".toList))))) (S.block (S.qStat (S.sReturn (S.lLast (S.mCall I (S.eGlob "tonumber") (S.lLast (S.mOne (S.eCell c_id)))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lLast (S.mOne S.eNil))) (S.gotos [] [])
      S.qEnd))) n)) n))) n)

theorem M_event_task_ok (I : Sem) (env0 : Env)
    (h_tonumber : env0.lookup "tonumber" = none) :
    CFn I (M_event_task I env0) ⟨["e"], false, M_event_task_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_e => CBs_end ((CK_block (CQ_local (CL_last (CM_one rfl (CE_or (CE_index (CE_cell rfl) CE_str) CE_str))) fun n => CBs_let fun c_s => CBs_end
      ((CQ_local (CL_last (CM_method (CE_cell rfl) (CL_last (CM_one rfl CE_str)))) fun n => CBs_let fun c_id => CBs_let fun c_rest => CBs_end
      ((CQ_stat (CS_if (CE_un (CE_cell rfl)) (CK_block (CQ_stat (CS_assign (CP_var (wCell_ok rfl) (CP_var (wCell_ok rfl) CP_nil)) (CL_last (CM_method (CE_cell rfl) (CL_last (CM_one rfl CE_str)))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_stat (CS_if (CE_and (CE_cell rfl) (CE_paren (CE_or (CE_bin (CE_cell rfl) CE_str) (CE_bin (CE_method (CM_method (CE_cell rfl) (CL_cons CE_num (CL_last (CM_one rfl CE_num))))) CE_str)))) (CK_block (CQ_stat (CS_return (CL_last (CM_call (CE_glob h_tonumber) (CL_last (CM_one rfl (CE_cell rfl))))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_stat (CS_return (CL_last (CM_one rfl CE_nil)))
      CQ_end rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) n)) n))) n)

def M_task_timing (I : Sem) (env0 : Env) (c_py c_util : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_r => S.let1 fun c_evs => S.letEnd ((S.block (S.qLocalFn "ts" ["k", "agg"] false ts_body (("evs", c_evs) :: ("r", c_r) :: env0) fun c_ts =>
      (S.qLocal (S.lCons (S.eNum (.int 0)) (S.lCons (S.eTable S.fNil) (S.lCons (S.eTable S.fNil) (S.lLast (S.mOne (S.eNum (.int 0))))))) fun n => S.let1 fun c_claims => S.let1 fun c_holders => S.let1 fun c_seen => S.let1 fun c_releases => S.letEnd
      ((S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mOne (S.eCell c_evs))))) fun n => S.let1 fun c__ => S.let1 fun c_e => S.letEnd ((S.block (S.qStat (S.sIf (S.eOr (S.eBin I .eq (S.eIndex I (S.eCell c_e) (S.eStr "kind".toList)) (S.eStr "claim".toList)) (S.eBin I .eq (S.eIndex I (S.eCell c_e) (S.eStr "kind".toList)) (S.eStr "spawn".toList))) (S.block (S.qStat (S.sAssign (S.pVar (S.wCell c_claims) S.pNil) (S.lLast (S.mOne (S.eBin I .add (S.eCell c_claims) (S.eNum (.int 1)))))) (S.gotos [] [])
          (S.qStat (S.sIf (S.eUn .not (S.eIndex I (S.eCell c_seen) (S.eIndex I (S.eCell c_e) (S.eStr "agent".toList)))) (S.block (S.qStat (S.sAssign (S.pIndex I (S.eCell c_seen) (S.eIndex I (S.eCell c_e) (S.eStr "agent".toList)) S.pNil) (S.lLast (S.mOne S.eTrue))) (S.gotos [] [])
            (S.qStat (S.sAssign (S.pIndex I (S.eCell c_holders) (S.eBin I .add (S.eUn .len (S.eCell c_holders)) (S.eNum (.int 1))) S.pNil) (S.lLast (S.mOne (S.eIndex I (S.eCell c_e) (S.eStr "agent".toList))))) (S.gotos [] [])
            S.qEnd))) (S.block S.qEnd)) (S.gotos [] [])
          S.qEnd))) (S.block (S.qStat (S.sIf (S.eBin I .eq (S.eIndex I (S.eCell c_e) (S.eStr "kind".toList)) (S.eStr "release".toList)) (S.block (S.qStat (S.sAssign (S.pVar (S.wCell c_releases) S.pNil) (S.lLast (S.mOne (S.eBin I .add (S.eCell c_releases) (S.eNum (.int 1)))))) (S.gotos [] [])
            S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
          S.qEnd))) (S.gotos [] [])
        S.qEnd)) n)) (S.gotos [] [])
      (S.qLocal (S.lLast (S.mOne (S.eOr (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "created_at".toList)))))) (S.eFirst (S.mCall I (S.eCell c_ts) (S.lCons (S.eStr "task-add".toList) (S.lLast (S.mOne (S.eIndex I (S.eGlob "math") (S.eStr "min".toList)))))))))) fun n => S.let1 fun c_created => S.letEnd
      ((S.qLocal (S.lLast (S.mOne (S.eOr (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "first_claimed_at".toList)))))) (S.eFirst (S.mCall I (S.eCell c_ts) (S.lCons (S.eStr "claim".toList) (S.lLast (S.mOne (S.eIndex I (S.eGlob "math") (S.eStr "min".toList)))))))))) fun n => S.let1 fun c_first => S.letEnd
      ((S.qLocal (S.lLast (S.mOne (S.eOr (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "done_at".toList)))))) (S.eParen (S.eOr (S.eAnd (S.eBin I .eq (S.eIndex I (S.eCell c_r) (S.eStr "state".toList)) (S.eStr "done".toList)) (S.eFirst (S.mCall I (S.eCell c_ts) (S.lCons (S.eStr "done".toList) (S.lLast (S.mOne (S.eIndex I (S.eGlob "math") (S.eStr "max".toList)))))))) S.eNil))))) fun n => S.let1 fun c_done => S.letEnd
      ((S.qLocal (S.lLast (S.mOne (S.eOr (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "dropped_at".toList)))))) (S.eParen (S.eOr (S.eAnd (S.eBin I .eq (S.eIndex I (S.eCell c_r) (S.eStr "state".toList)) (S.eStr "dropped".toList)) (S.eFirst (S.mCall I (S.eCell c_ts) (S.lCons (S.eStr "drop".toList) (S.lLast (S.mOne (S.eIndex I (S.eGlob "math") (S.eStr "max".toList)))))))) S.eNil))))) fun n => S.let1 fun c_dropped => S.letEnd
      ((S.qLocal (S.lLast (S.mOne (S.eOr (S.eOr (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eCell c_done))))) (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eCell c_dropped)))))) (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "now".toList)) S.lNil))))) fun n => S.let1 fun c_stop => S.letEnd
      ((S.qLocal (S.lCons (S.eNum (.int 0)) (S.lLast (S.mOne S.eNil))) fun n => S.let1 fun c_blocked => S.let1 fun c_start => S.letEnd
      ((S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mOne (S.eCell c_evs))))) fun n => S.let1 fun c__1 => S.let1 fun c_e1 => S.letEnd ((S.block (S.qStat (S.sIf (S.eAnd (S.eBin I .eq (S.eIndex I (S.eCell c_e1) (S.eStr "kind".toList)) (S.eStr "block".toList)) (S.eBin I .eq (S.eCell c_start) S.eNil)) (S.block (S.qStat (S.sAssign (S.pVar (S.wCell c_start) S.pNil) (S.lLast (S.mOne (S.eIndex I (S.eCell c_e1) (S.eStr "ts".toList))))) (S.gotos [] [])
          S.qEnd)) (S.block (S.qStat (S.sIf (S.eAnd (S.eBin I .eq (S.eIndex I (S.eCell c_e1) (S.eStr "kind".toList)) (S.eStr "unblock".toList)) (S.eBin I .ne (S.eCell c_start) S.eNil)) (S.block (S.qStat (S.sAssign (S.pVar (S.wCell c_blocked) (S.pVar (S.wCell c_start) S.pNil)) (S.lCons (S.eBin I .sub (S.eBin I .add (S.eCell c_blocked) (S.eIndex I (S.eCell c_e1) (S.eStr "ts".toList))) (S.eCell c_start)) (S.lLast (S.mOne S.eNil)))) (S.gotos [] [])
            S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
          S.qEnd))) (S.gotos [] [])
        S.qEnd)) n)) (S.gotos [] [])
      (S.qStat (S.sIf (S.eAnd (S.eBin I .ne (S.eCell c_start) S.eNil) (S.eBin I .eq (S.eIndex I (S.eCell c_r) (S.eStr "state".toList)) (S.eStr "blocked".toList))) (S.block (S.qStat (S.sAssign (S.pVar (S.wCell c_blocked) S.pNil) (S.lLast (S.mOne (S.eBin I .sub (S.eBin I .add (S.eCell c_blocked) (S.eCell c_stop)) (S.eCell c_start))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qLocalFn "span" ["a", "b"] false span_body (("start", c_start) :: ("blocked", c_blocked) :: ("stop", c_stop) :: ("dropped", c_dropped) :: ("done", c_done) :: ("first", c_first) :: ("created", c_created) :: ("releases", c_releases) :: ("seen", c_seen) :: ("holders", c_holders) :: ("claims", c_claims) :: ("ts", c_ts) :: ("evs", c_evs) :: ("r", c_r) :: env0) fun c_span =>
      (S.qStat (S.sReturn (S.lLast (S.mOne (S.eTable (S.fNamed "created_at" (S.eCell c_created) (S.fNamed "first_claimed_at" (S.eCell c_first) (S.fNamed "done_at" (S.eCell c_done) (S.fNamed "dropped_at" (S.eCell c_dropped) (S.fNamed "queue_wait_s" (S.eFirst (S.mCall I (S.eCell c_span) (S.lCons (S.eCell c_created) (S.lLast (S.mOne (S.eCell c_first)))))) (S.fNamed "work_s" (S.eFirst (S.mCall I (S.eCell c_span) (S.lCons (S.eCell c_first) (S.lLast (S.mOne (S.eCell c_done)))))) (S.fNamed "total_s" (S.eFirst (S.mCall I (S.eCell c_span) (S.lCons (S.eCell c_created) (S.lLast (S.mOne (S.eCell c_done)))))) (S.fNamed "blocked_s" (S.eCell c_blocked) (S.fNamed "claims" (S.eCell c_claims) (S.fNamed "releases" (S.eCell c_releases) (S.fNamed "holders" (S.eCell c_holders) (S.fNamed "claim_ctx" (S.eIndex I (S.eCell c_r) (S.eStr "claim_ctx".toList)) (S.fNamed "done_ctx" (S.eIndex I (S.eCell c_r) (S.eStr "done_ctx".toList)) (S.fNamed "pr" (S.eIndex I (S.eCell c_r) (S.eStr "pr".toList)) (S.fNamed "merged_at" (S.eIndex I (S.eCell c_r) (S.eStr "merged_at".toList)) (S.fNamed "ci_conclusion" (S.eIndex I (S.eCell c_r) (S.eStr "ci_conclusion".toList)) (S.fNamed "merge_to_green_s" (S.eFirst (S.mCall I (S.eCell c_span) (S.lCons (S.eIndex I (S.eCell c_r) (S.eStr "merged_at".toList)) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "ci_green_at".toList))))))) S.fNil))))))))))))))))))))) (S.gotos [] [])
      S.qEnd)))) n)) n)) n)) n)) n)) n))) n)))) n)

theorem M_task_timing_ok (I : Sem) (env0 : Env) (c_py c_util : Nat)
    (h_py : env0.lookup "py" = some c_py)
    (h_util : env0.lookup "util" = some c_util)
    (h_ipairs : env0.lookup "ipairs" = none)
    (h_math : env0.lookup "math" = none) :
    CFn I (M_task_timing I env0 c_py c_util) ⟨["r", "evs"], false, M_task_timing_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_r => CBs_let fun c_evs => CBs_end ((CK_block (CQ_localFn (by rfl) fun c_ts =>
      (CQ_local (CL_cons CE_num (CL_cons (CE_table CF_nil) (CL_cons (CE_table CF_nil) (CL_last (CM_one rfl CE_num))))) fun n => CBs_let fun c_claims => CBs_let fun c_holders => CBs_let fun c_seen => CBs_let fun c_releases => CBs_end
      ((CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_one rfl (CE_cell rfl))))) fun n => CBs_let fun c__ => CBs_let fun c_e => CBs_end ((CK_block (CQ_stat (CS_if (CE_or (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str)) (CK_block (CQ_stat (CS_assign (CP_var (wCell_ok rfl) CP_nil) (CL_last (CM_one rfl (CE_bin (CE_cell rfl) CE_num))))
          (CQ_stat (CS_if (CE_un (CE_index (CE_cell rfl) (CE_index (CE_cell rfl) CE_str))) (CK_block (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_index (CE_cell rfl) CE_str) CP_nil) (CL_last (CM_one rfl CE_true)))
            (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_bin (CE_un (CE_cell rfl)) CE_num) CP_nil) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))
            CQ_end rfl rfl rfl) rfl rfl rfl)) (CK_block CQ_end))
          CQ_end rfl rfl rfl) rfl rfl rfl)) (CK_block (CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_stat (CS_assign (CP_var (wCell_ok rfl) CP_nil) (CL_last (CM_one rfl (CE_bin (CE_cell rfl) CE_num))))
            CQ_end rfl rfl rfl)) (CK_block CQ_end))
          CQ_end rfl rfl rfl)))
        CQ_end rfl rfl rfl)) n))
      (CQ_local (CL_last (CM_one rfl (CE_or (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CE_call (CM_call (CE_cell rfl) (CL_cons CE_str (CL_last (CM_one rfl (CE_index (CE_glob h_math) CE_str))))))))) fun n => CBs_let fun c_created => CBs_end
      ((CQ_local (CL_last (CM_one rfl (CE_or (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CE_call (CM_call (CE_cell rfl) (CL_cons CE_str (CL_last (CM_one rfl (CE_index (CE_glob h_math) CE_str))))))))) fun n => CBs_let fun c_first => CBs_end
      ((CQ_local (CL_last (CM_one rfl (CE_or (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CE_paren (CE_or (CE_and (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CE_call (CM_call (CE_cell rfl) (CL_cons CE_str (CL_last (CM_one rfl (CE_index (CE_glob h_math) CE_str))))))) CE_nil))))) fun n => CBs_let fun c_done => CBs_end
      ((CQ_local (CL_last (CM_one rfl (CE_or (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CE_paren (CE_or (CE_and (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CE_call (CM_call (CE_cell rfl) (CL_cons CE_str (CL_last (CM_one rfl (CE_index (CE_glob h_math) CE_str))))))) CE_nil))))) fun n => CBs_let fun c_dropped => CBs_end
      ((CQ_local (CL_last (CM_one rfl (CE_or (CE_or (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_cell rfl))))) (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_cell rfl)))))) (CE_call (CM_call (CE_index (CE_cell h_util) CE_str) CL_nil))))) fun n => CBs_let fun c_stop => CBs_end
      ((CQ_local (CL_cons CE_num (CL_last (CM_one rfl CE_nil))) fun n => CBs_let fun c_blocked => CBs_let fun c_start => CBs_end
      ((CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_one rfl (CE_cell rfl))))) fun n => CBs_let fun c__1 => CBs_let fun c_e1 => CBs_end ((CK_block (CQ_stat (CS_if (CE_and (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CE_bin (CE_cell rfl) CE_nil)) (CK_block (CQ_stat (CS_assign (CP_var (wCell_ok rfl) CP_nil) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))
          CQ_end rfl rfl rfl)) (CK_block (CQ_stat (CS_if (CE_and (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CE_bin (CE_cell rfl) CE_nil)) (CK_block (CQ_stat (CS_assign (CP_var (wCell_ok rfl) (CP_var (wCell_ok rfl) CP_nil)) (CL_cons (CE_bin (CE_bin (CE_cell rfl) (CE_index (CE_cell rfl) CE_str)) (CE_cell rfl)) (CL_last (CM_one rfl CE_nil))))
            CQ_end rfl rfl rfl)) (CK_block CQ_end))
          CQ_end rfl rfl rfl)))
        CQ_end rfl rfl rfl)) n))
      (CQ_stat (CS_if (CE_and (CE_bin (CE_cell rfl) CE_nil) (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str)) (CK_block (CQ_stat (CS_assign (CP_var (wCell_ok rfl) CP_nil) (CL_last (CM_one rfl (CE_bin (CE_bin (CE_cell rfl) (CE_cell rfl)) (CE_cell rfl)))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_localFn (by rfl) fun c_span =>
      (CQ_stat (CS_return (CL_last (CM_one rfl (CE_table (CF_named (CE_cell rfl) (CF_named (CE_cell rfl) (CF_named (CE_cell rfl) (CF_named (CE_cell rfl) (CF_named (CE_call (CM_call (CE_cell rfl) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl)))))) (CF_named (CE_call (CM_call (CE_cell rfl) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl)))))) (CF_named (CE_call (CM_call (CE_cell rfl) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl)))))) (CF_named (CE_cell rfl) (CF_named (CE_cell rfl) (CF_named (CE_cell rfl) (CF_named (CE_cell rfl) (CF_named (CE_index (CE_cell rfl) CE_str) (CF_named (CE_index (CE_cell rfl) CE_str) (CF_named (CE_index (CE_cell rfl) CE_str) (CF_named (CE_index (CE_cell rfl) CE_str) (CF_named (CE_index (CE_cell rfl) CE_str) (CF_named (CE_call (CM_call (CE_cell rfl) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))) CF_nil)))))))))))))))))))))
      CQ_end rfl rfl rfl)) rfl rfl rfl) rfl rfl rfl) n)) n)) n)) n)) n)) n)) rfl rfl rfl) n)))) n)

def M_task_events (I : Sem) (env0 : Env) (c_M : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_c => S.let1 fun c_tid => S.letEnd ((S.block (S.qLocal (S.lLast (S.mOne (S.eTable S.fNil))) fun n => S.let1 fun c_r => S.letEnd
      ((S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mMethod I (S.eCell c_c) "all" (S.lLast (S.mOne (S.eBin I .concat (S.eStr "select ts,agent,kind,data from event where kind in ('".toList) (S.eBin I .concat (S.eFirst (S.mCall I (S.eIndex I (S.eGlob "table") (S.eStr "concat".toList)) (S.lCons (S.eIndex I (S.eCell c_M) (S.eStr "TASK_KINDS".toList)) (S.lLast (S.mOne (S.eStr "','".toList)))))) (S.eStr "') order by id".toList))))))))) fun n => S.let1 fun c__ => S.let1 fun c_e => S.letEnd ((S.block (S.qStat (S.sIf (S.eBin I .eq (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "event_task".toList)) (S.lLast (S.mOne (S.eCell c_e))))) (S.eCell c_tid)) (S.block (S.qStat (S.sAssign (S.pIndex I (S.eCell c_r) (S.eBin I .add (S.eUn .len (S.eCell c_r)) (S.eNum (.int 1))) S.pNil) (S.lLast (S.mOne (S.eCell c_e)))) (S.gotos [] [])
          S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
        S.qEnd)) n)) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lLast (S.mOne (S.eCell c_r)))) (S.gotos [] [])
      S.qEnd)) n))) n)

theorem M_task_events_ok (I : Sem) (env0 : Env) (c_M : Nat)
    (h_M : env0.lookup "M" = some c_M)
    (h_ipairs : env0.lookup "ipairs" = none)
    (h_table : env0.lookup "table" = none) :
    CFn I (M_task_events I env0 c_M) ⟨["c", "tid"], false, M_task_events_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_c => CBs_let fun c_tid => CBs_end ((CK_block (CQ_local (CL_last (CM_one rfl (CE_table CF_nil))) fun n => CBs_let fun c_r => CBs_end
      ((CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_method (CE_cell rfl) (CL_last (CM_one rfl (CE_bin CE_str (CE_bin (CE_call (CM_call (CE_index (CE_glob h_table) CE_str) (CL_cons (CE_index (CE_cell h_M) CE_str) (CL_last (CM_one rfl CE_str))))) CE_str)))))))) fun n => CBs_let fun c__ => CBs_let fun c_e => CBs_end ((CK_block (CQ_stat (CS_if (CE_bin (CE_call (CM_call (CE_index (CE_cell h_M) CE_str) (CL_last (CM_one rfl (CE_cell rfl))))) (CE_cell rfl)) (CK_block (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_bin (CE_un (CE_cell rfl)) CE_num) CP_nil) (CL_last (CM_one rfl (CE_cell rfl))))
          CQ_end rfl rfl rfl)) (CK_block CQ_end))
        CQ_end rfl rfl rfl)) n))
      (CQ_stat (CS_return (CL_last (CM_one rfl (CE_cell rfl))))
      CQ_end rfl rfl rfl) rfl rfl rfl) n))) n)

def M_deps_of (I : Sem) (env0 : Env) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_r => S.letEnd ((S.block (S.qLocal (S.lLast (S.mOne (S.eTable S.fNil))) fun n => S.let1 fun c_r2 => S.letEnd
      ((S.qStat (S.sForIn I (S.lLast (S.mMethod I (S.eParen (S.eOr (S.eIndex I (S.eCell c_r) (S.eStr "deps".toList)) (S.eStr "".toList))) "gmatch" (S.lLast (S.mOne (S.eStr "[^,]+".toList))))) fun n => S.let1 fun c_x => S.letEnd ((S.block (S.qStat (S.sAssign (S.pIndex I (S.eCell c_r2) (S.eBin I .add (S.eUn .len (S.eCell c_r2)) (S.eNum (.int 1))) S.pNil) (S.lLast (S.mCall I (S.eGlob "tonumber") (S.lLast (S.mOne (S.eCell c_x)))))) (S.gotos [] [])
        S.qEnd)) n)) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lLast (S.mOne (S.eCell c_r2)))) (S.gotos [] [])
      S.qEnd)) n))) n)

theorem M_deps_of_ok (I : Sem) (env0 : Env)
    (h_tonumber : env0.lookup "tonumber" = none) :
    CFn I (M_deps_of I env0) ⟨["r"], false, M_deps_of_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_r => CBs_end ((CK_block (CQ_local (CL_last (CM_one rfl (CE_table CF_nil))) fun n => CBs_let fun c_r2 => CBs_end
      ((CQ_stat (CS_forin (CL_last (CM_method (CE_paren (CE_or (CE_index (CE_cell rfl) CE_str) CE_str)) (CL_last (CM_one rfl CE_str)))) fun n => CBs_let fun c_x => CBs_end ((CK_block (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_bin (CE_un (CE_cell rfl)) CE_num) CP_nil) (CL_last (CM_call (CE_glob h_tonumber) (CL_last (CM_one rfl (CE_cell rfl))))))
        CQ_end rfl rfl rfl)) n))
      (CQ_stat (CS_return (CL_last (CM_one rfl (CE_cell rfl))))
      CQ_end rfl rfl rfl) rfl rfl rfl) n))) n)

def M_undone (I : Sem) (env0 : Env) (c_M : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_c => S.let1 fun c_r => S.letEnd ((S.block (S.qLocal (S.lCons (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "deps_of".toList)) (S.lLast (S.mOne (S.eCell c_r))))) (S.lLast (S.mOne (S.eTable S.fNil)))) fun n => S.let1 fun c_deps => S.let1 fun c_out => S.letEnd
      ((S.qStat (S.sIf (S.eBin I .eq (S.eUn .len (S.eCell c_deps)) (S.eNum (.int 0))) (S.block (S.qStat (S.sReturn (S.lLast (S.mOne (S.eCell c_out)))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qLocal (S.lLast (S.mOne (S.eTable S.fNil))) fun n => S.let1 fun c_q => S.letEnd
      ((S.qStat (S.sForNum (S.eNum (.int 1)) (S.eUn .len (S.eCell c_deps)) none fun c_i => (S.block (S.qStat (S.sAssign (S.pIndex I (S.eCell c_q) (S.eCell c_i) S.pNil) (S.lLast (S.mOne (S.eStr "?".toList)))) (S.gotos [] [])
        S.qEnd))) (S.gotos [] [])
      (S.qLocal (S.lLast (S.mOne (S.eTable S.fNil))) fun n => S.let1 fun c_st => S.letEnd
      ((S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mMethod I (S.eCell c_c) "all" (S.lCons (S.eBin I .concat (S.eStr "select * from task where id in (".toList) (S.eBin I .concat (S.eFirst (S.mCall I (S.eIndex I (S.eGlob "table") (S.eStr "concat".toList)) (S.lCons (S.eCell c_q) (S.lLast (S.mOne (S.eStr ",".toList)))))) (S.eStr ") and state!='done'".toList))) (S.lLast (S.mCall I (S.eGlob "unpack") (S.lLast (S.mOne (S.eCell c_deps)))))))))) fun n => S.let1 fun c__ => S.let1 fun c_x => S.letEnd ((S.block (S.qStat (S.sAssign (S.pIndex I (S.eCell c_st) (S.eIndex I (S.eCell c_x) (S.eStr "id".toList)) S.pNil) (S.lLast (S.mOne (S.eCell c_x)))) (S.gotos [] [])
        S.qEnd)) n)) (S.gotos [] [])
      (S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mOne (S.eCell c_deps))))) fun n => S.let1 fun c__1 => S.let1 fun c_i1 => S.letEnd ((S.block (S.qStat (S.sIf (S.eIndex I (S.eCell c_st) (S.eCell c_i1)) (S.block (S.qStat (S.sAssign (S.pIndex I (S.eCell c_out) (S.eBin I .add (S.eUn .len (S.eCell c_out)) (S.eNum (.int 1))) S.pNil) (S.lLast (S.mOne (S.eIndex I (S.eCell c_st) (S.eCell c_i1))))) (S.gotos [] [])
          S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
        S.qEnd)) n)) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lLast (S.mOne (S.eCell c_out)))) (S.gotos [] [])
      S.qEnd))) n))) n))) n))) n)

theorem M_undone_ok (I : Sem) (env0 : Env) (c_M : Nat)
    (h_M : env0.lookup "M" = some c_M)
    (h_ipairs : env0.lookup "ipairs" = none)
    (h_table : env0.lookup "table" = none)
    (h_unpack : env0.lookup "unpack" = none) :
    CFn I (M_undone I env0 c_M) ⟨["c", "r"], false, M_undone_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_c => CBs_let fun c_r => CBs_end ((CK_block (CQ_local (CL_cons (CE_call (CM_call (CE_index (CE_cell h_M) CE_str) (CL_last (CM_one rfl (CE_cell rfl))))) (CL_last (CM_one rfl (CE_table CF_nil)))) fun n => CBs_let fun c_deps => CBs_let fun c_out => CBs_end
      ((CQ_stat (CS_if (CE_bin (CE_un (CE_cell rfl)) CE_num) (CK_block (CQ_stat (CS_return (CL_last (CM_one rfl (CE_cell rfl))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_local (CL_last (CM_one rfl (CE_table CF_nil))) fun n => CBs_let fun c_q => CBs_end
      ((CQ_stat (CS_fornum CE_num (CE_un (CE_cell rfl)) trivial fun c_i => (CK_block (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_cell rfl) CP_nil) (CL_last (CM_one rfl CE_str)))
        CQ_end rfl rfl rfl)))
      (CQ_local (CL_last (CM_one rfl (CE_table CF_nil))) fun n => CBs_let fun c_st => CBs_end
      ((CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_method (CE_cell rfl) (CL_cons (CE_bin CE_str (CE_bin (CE_call (CM_call (CE_index (CE_glob h_table) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl CE_str))))) CE_str)) (CL_last (CM_call (CE_glob h_unpack) (CL_last (CM_one rfl (CE_cell rfl)))))))))) fun n => CBs_let fun c__ => CBs_let fun c_x => CBs_end ((CK_block (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_index (CE_cell rfl) CE_str) CP_nil) (CL_last (CM_one rfl (CE_cell rfl))))
        CQ_end rfl rfl rfl)) n))
      (CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_one rfl (CE_cell rfl))))) fun n => CBs_let fun c__1 => CBs_let fun c_i1 => CBs_end ((CK_block (CQ_stat (CS_if (CE_index (CE_cell rfl) (CE_cell rfl)) (CK_block (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_bin (CE_un (CE_cell rfl)) CE_num) CP_nil) (CL_last (CM_one rfl (CE_index (CE_cell rfl) (CE_cell rfl)))))
          CQ_end rfl rfl rfl)) (CK_block CQ_end))
        CQ_end rfl rfl rfl)) n))
      (CQ_stat (CS_return (CL_last (CM_one rfl (CE_cell rfl))))
      CQ_end rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) n)) rfl rfl rfl) n)) rfl rfl rfl) n))) n)

def M_waiters (I : Sem) (env0 : Env) (c_d : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_c => S.let1 fun c_tid => S.letEnd ((S.block (S.qStat (S.sReturn (S.lLast (S.mMethod I (S.eCell c_c) "all" (S.lCons (S.eStr "select * from task where state='open' and ','||deps||',' like ?".toList) (S.lLast (S.mOne (S.eBin I .concat (S.eStr "%,".toList) (S.eBin I .concat (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eCell c_tid))))) (S.eStr ",%".toList))))))))) (S.gotos [] [])
      S.qEnd)) n)

theorem M_waiters_ok (I : Sem) (env0 : Env) (c_d : Nat)
    (h_d : env0.lookup "d" = some c_d) :
    CFn I (M_waiters I env0 c_d) ⟨["c", "tid"], false, M_waiters_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_c => CBs_let fun c_tid => CBs_end ((CK_block (CQ_stat (CS_return (CL_last (CM_method (CE_cell rfl) (CL_cons CE_str (CL_last (CM_one rfl (CE_bin CE_str (CE_bin (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_cell rfl))))) CE_str))))))))
      CQ_end rfl rfl rfl)) n)

def M_dep_path (I : Sem) (env0 : Env) (c_M : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_c => S.let1 fun c_start => S.let1 fun c_target => S.letEnd ((S.block (S.qLocal (S.lCons (S.eTable S.fNil) (S.lLast (S.mOne (S.eTable (S.fLast (S.mOne (S.eTable (S.fLast (S.mOne (S.eCell c_start)))))))))) fun n => S.let1 fun c_seen => S.let1 fun c_stack => S.letEnd
      ((S.qStat (S.sWhile (S.eBin I .gt (S.eUn .len (S.eCell c_stack)) (S.eNum (.int 0))) (S.block (S.qLocal (S.lLast (S.mCall I (S.eIndex I (S.eGlob "table") (S.eStr "remove".toList)) (S.lLast (S.mOne (S.eCell c_stack))))) fun n => S.let1 fun c_path => S.letEnd
        ((S.qLocal (S.lLast (S.mOne (S.eIndex I (S.eCell c_path) (S.eUn .len (S.eCell c_path))))) fun n => S.let1 fun c_last => S.letEnd
        ((S.qStat (S.sIf (S.eBin I .eq (S.eCell c_last) (S.eCell c_target)) (S.block (S.qStat (S.sReturn (S.lLast (S.mOne (S.eCell c_path)))) (S.gotos [] [])
          S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
        (S.qStat (S.sIf (S.eUn .not (S.eIndex I (S.eCell c_seen) (S.eCell c_last))) (S.block (S.qStat (S.sAssign (S.pIndex I (S.eCell c_seen) (S.eCell c_last) S.pNil) (S.lLast (S.mOne S.eTrue))) (S.gotos [] [])
          (S.qLocal (S.lLast (S.mMethod I (S.eCell c_c) "one" (S.lCons (S.eStr "select * from task where id=?".toList) (S.lLast (S.mOne (S.eCell c_last)))))) fun n => S.let1 fun c_r => S.letEnd
          ((S.qLocal (S.lLast (S.mOne (S.eOr (S.eAnd (S.eCell c_r) (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "deps_of".toList)) (S.lLast (S.mOne (S.eCell c_r)))))) (S.eTable S.fNil)))) fun n => S.let1 fun c_deps => S.letEnd
          ((S.qStat (S.sForNum (S.eUn .len (S.eCell c_deps)) (S.eNum (.int 1)) (some (S.eNum (.int (-1)))) fun c_i => (S.block (S.qLocal (S.lLast (S.mOne (S.eTable (S.fLast (S.mCall I (S.eGlob "unpack") (S.lLast (S.mOne (S.eCell c_path)))))))) fun n => S.let1 fun c_p => S.letEnd
            ((S.qStat (S.sAssign (S.pIndex I (S.eCell c_p) (S.eBin I .add (S.eUn .len (S.eCell c_p)) (S.eNum (.int 1))) S.pNil) (S.lLast (S.mOne (S.eIndex I (S.eCell c_deps) (S.eCell c_i))))) (S.gotos [] [])
            (S.qStat (S.sAssign (S.pIndex I (S.eCell c_stack) (S.eBin I .add (S.eUn .len (S.eCell c_stack)) (S.eNum (.int 1))) S.pNil) (S.lLast (S.mOne (S.eCell c_p)))) (S.gotos [] [])
            S.qEnd)) n)))) (S.gotos [] [])
          S.qEnd) n)) n)))) (S.block S.qEnd)) (S.gotos [] [])
        S.qEnd)) n)) n)))) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lLast (S.mOne S.eNil))) (S.gotos [] [])
      S.qEnd)) n))) n)

theorem M_dep_path_ok (I : Sem) (env0 : Env) (c_M : Nat)
    (h_M : env0.lookup "M" = some c_M)
    (h_table : env0.lookup "table" = none)
    (h_unpack : env0.lookup "unpack" = none) :
    CFn I (M_dep_path I env0 c_M) ⟨["c", "start", "target"], false, M_dep_path_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_c => CBs_let fun c_start => CBs_let fun c_target => CBs_end ((CK_block (CQ_local (CL_cons (CE_table CF_nil) (CL_last (CM_one rfl (CE_table (CF_last (CM_one rfl (CE_table (CF_last (CM_one rfl (CE_cell rfl)))))))))) fun n => CBs_let fun c_seen => CBs_let fun c_stack => CBs_end
      ((CQ_stat (CS_while (CE_bin (CE_un (CE_cell rfl)) CE_num) (CK_block (CQ_local (CL_last (CM_call (CE_index (CE_glob h_table) CE_str) (CL_last (CM_one rfl (CE_cell rfl))))) fun n => CBs_let fun c_path => CBs_end
        ((CQ_local (CL_last (CM_one rfl (CE_index (CE_cell rfl) (CE_un (CE_cell rfl))))) fun n => CBs_let fun c_last => CBs_end
        ((CQ_stat (CS_if (CE_bin (CE_cell rfl) (CE_cell rfl)) (CK_block (CQ_stat (CS_return (CL_last (CM_one rfl (CE_cell rfl))))
          CQ_end rfl rfl rfl)) (CK_block CQ_end))
        (CQ_stat (CS_if (CE_un (CE_index (CE_cell rfl) (CE_cell rfl))) (CK_block (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_cell rfl) CP_nil) (CL_last (CM_one rfl CE_true)))
          (CQ_local (CL_last (CM_method (CE_cell rfl) (CL_cons CE_str (CL_last (CM_one rfl (CE_cell rfl)))))) fun n => CBs_let fun c_r => CBs_end
          ((CQ_local (CL_last (CM_one rfl (CE_or (CE_and (CE_cell rfl) (CE_call (CM_call (CE_index (CE_cell h_M) CE_str) (CL_last (CM_one rfl (CE_cell rfl)))))) (CE_table CF_nil)))) fun n => CBs_let fun c_deps => CBs_end
          ((CQ_stat (CS_fornum (CE_un (CE_cell rfl)) CE_num CE_num fun c_i => (CK_block (CQ_local (CL_last (CM_one rfl (CE_table (CF_last (CM_call (CE_glob h_unpack) (CL_last (CM_one rfl (CE_cell rfl)))))))) fun n => CBs_let fun c_p => CBs_end
            ((CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_bin (CE_un (CE_cell rfl)) CE_num) CP_nil) (CL_last (CM_one rfl (CE_index (CE_cell rfl) (CE_cell rfl)))))
            (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_bin (CE_un (CE_cell rfl)) CE_num) CP_nil) (CL_last (CM_one rfl (CE_cell rfl))))
            CQ_end rfl rfl rfl) rfl rfl rfl) n))))
          CQ_end rfl rfl rfl) n)) n)) rfl rfl rfl)) (CK_block CQ_end))
        CQ_end rfl rfl rfl) rfl rfl rfl) n)) n))))
      (CQ_stat (CS_return (CL_last (CM_one rfl CE_nil)))
      CQ_end rfl rfl rfl) rfl rfl rfl) n))) n)

def M_pool (I : Sem) (env0 : Env) (c_M : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_c => S.letEnd ((S.block (S.qStat (S.sReturn (S.lLast (S.mMethod I (S.eCell c_c) "all" (S.lCons (S.eBin I .concat (S.eStr "select * from task t where state='open' and not exists (select 1 from task d where d.state!='done' ".toList) (S.eStr "and ','||t.deps||',' like '%,'||d.id||',%') order by title like ? desc, id".toList)) (S.lLast (S.mOne (S.eBin I .concat (S.eIndex I (S.eCell c_M) (S.eStr "RED_TASK".toList)) (S.eStr "%".toList)))))))) (S.gotos [] [])
      S.qEnd)) n)

theorem M_pool_ok (I : Sem) (env0 : Env) (c_M : Nat)
    (h_M : env0.lookup "M" = some c_M) :
    CFn I (M_pool I env0 c_M) ⟨["c"], false, M_pool_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_c => CBs_end ((CK_block (CQ_stat (CS_return (CL_last (CM_method (CE_cell rfl) (CL_cons (CE_bin CE_str CE_str) (CL_last (CM_one rfl (CE_bin (CE_index (CE_cell h_M) CE_str) CE_str)))))))
      CQ_end rfl rfl rfl)) n)

def M_dep_lines (I : Sem) (env0 : Env) (c_M c_d : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_c => S.let1 fun c_r => S.letEnd ((S.block (S.qLocal (S.lLast (S.mOne (S.eTable S.fNil))) fun n => S.let1 fun c_st => S.letEnd
      ((S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mMethod I (S.eCell c_c) "all" (S.lLast (S.mOne (S.eStr "select id,state from task".toList))))))) fun n => S.let1 fun c__ => S.let1 fun c_x => S.letEnd ((S.block (S.qStat (S.sAssign (S.pIndex I (S.eCell c_st) (S.eIndex I (S.eCell c_x) (S.eStr "id".toList)) S.pNil) (S.lLast (S.mOne (S.eIndex I (S.eCell c_x) (S.eStr "state".toList))))) (S.gotos [] [])
        S.qEnd)) n)) (S.gotos [] [])
      (S.qLocal (S.lCons (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "deps_of".toList)) (S.lLast (S.mOne (S.eCell c_r))))) (S.lLast (S.mOne (S.eStr "".toList)))) fun n => S.let1 fun c_deps => S.let1 fun c_out => S.letEnd
      ((S.qStat (S.sIf (S.eBin I .gt (S.eUn .len (S.eCell c_deps)) (S.eNum (.int 0))) (S.block (S.qLocal (S.lLast (S.mOne (S.eTable S.fNil))) fun n => S.let1 fun c_p => S.letEnd
        ((S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mOne (S.eCell c_deps))))) fun n => S.let1 fun c_i => S.let1 fun c_x1 => S.letEnd ((S.block (S.qStat (S.sAssign (S.pIndex I (S.eCell c_p) (S.eCell c_i) S.pNil) (S.lLast (S.mOne (S.eBin I .concat (S.eStr "#".toList) (S.eBin I .concat (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eCell c_x1))))) (S.eBin I .concat (S.eStr " ".toList) (S.eParen (S.eOr (S.eIndex I (S.eCell c_st) (S.eCell c_x1)) (S.eStr "missing".toList))))))))) (S.gotos [] [])
          S.qEnd)) n)) (S.gotos [] [])
        (S.qStat (S.sAssign (S.pVar (S.wCell c_out) S.pNil) (S.lLast (S.mOne (S.eBin I .concat (S.eStr "\nafter: ".toList) (S.eFirst (S.mCall I (S.eIndex I (S.eGlob "table") (S.eStr "concat".toList)) (S.lCons (S.eCell c_p) (S.lLast (S.mOne (S.eStr ", ".toList)))))))))) (S.gotos [] [])
        S.qEnd)) n))) (S.block S.qEnd)) (S.gotos [] [])
      (S.qLocal (S.lLast (S.mOne (S.eOr (S.eAnd (S.eBin I .ne (S.eIndex I (S.eCell c_r) (S.eStr "state".toList)) (S.eStr "done".toList)) (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "waiters".toList)) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "id".toList)))))))) (S.eTable S.fNil)))) fun n => S.let1 fun c_w => S.letEnd
      ((S.qStat (S.sIf (S.eBin I .gt (S.eUn .len (S.eCell c_w)) (S.eNum (.int 0))) (S.block (S.qLocal (S.lLast (S.mOne (S.eTable S.fNil))) fun n => S.let1 fun c_p1 => S.letEnd
        ((S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mOne (S.eCell c_w))))) fun n => S.let1 fun c_i1 => S.let1 fun c_x2 => S.letEnd ((S.block (S.qStat (S.sAssign (S.pIndex I (S.eCell c_p1) (S.eCell c_i1) S.pNil) (S.lLast (S.mOne (S.eBin I .concat (S.eStr "#".toList) (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_x2) (S.eStr "id".toList)))))))))) (S.gotos [] [])
          S.qEnd)) n)) (S.gotos [] [])
        (S.qStat (S.sAssign (S.pVar (S.wCell c_out) S.pNil) (S.lLast (S.mOne (S.eBin I .concat (S.eCell c_out) (S.eBin I .concat (S.eStr "\nblocks: ".toList) (S.eFirst (S.mCall I (S.eIndex I (S.eGlob "table") (S.eStr "concat".toList)) (S.lCons (S.eCell c_p1) (S.lLast (S.mOne (S.eStr ", ".toList))))))))))) (S.gotos [] [])
        S.qEnd)) n))) (S.block S.qEnd)) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lLast (S.mOne (S.eCell c_out)))) (S.gotos [] [])
      S.qEnd)) n))) n))) n))) n)

theorem M_dep_lines_ok (I : Sem) (env0 : Env) (c_M c_d : Nat)
    (h_M : env0.lookup "M" = some c_M)
    (h_d : env0.lookup "d" = some c_d)
    (h_ipairs : env0.lookup "ipairs" = none)
    (h_table : env0.lookup "table" = none) :
    CFn I (M_dep_lines I env0 c_M c_d) ⟨["c", "r"], false, M_dep_lines_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_c => CBs_let fun c_r => CBs_end ((CK_block (CQ_local (CL_last (CM_one rfl (CE_table CF_nil))) fun n => CBs_let fun c_st => CBs_end
      ((CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_method (CE_cell rfl) (CL_last (CM_one rfl CE_str)))))) fun n => CBs_let fun c__ => CBs_let fun c_x => CBs_end ((CK_block (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_index (CE_cell rfl) CE_str) CP_nil) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))
        CQ_end rfl rfl rfl)) n))
      (CQ_local (CL_cons (CE_call (CM_call (CE_index (CE_cell h_M) CE_str) (CL_last (CM_one rfl (CE_cell rfl))))) (CL_last (CM_one rfl CE_str))) fun n => CBs_let fun c_deps => CBs_let fun c_out => CBs_end
      ((CQ_stat (CS_if (CE_bin (CE_un (CE_cell rfl)) CE_num) (CK_block (CQ_local (CL_last (CM_one rfl (CE_table CF_nil))) fun n => CBs_let fun c_p => CBs_end
        ((CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_one rfl (CE_cell rfl))))) fun n => CBs_let fun c_i => CBs_let fun c_x1 => CBs_end ((CK_block (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_cell rfl) CP_nil) (CL_last (CM_one rfl (CE_bin CE_str (CE_bin (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_cell rfl))))) (CE_bin CE_str (CE_paren (CE_or (CE_index (CE_cell rfl) (CE_cell rfl)) CE_str))))))))
          CQ_end rfl rfl rfl)) n))
        (CQ_stat (CS_assign (CP_var (wCell_ok rfl) CP_nil) (CL_last (CM_one rfl (CE_bin CE_str (CE_call (CM_call (CE_index (CE_glob h_table) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl CE_str)))))))))
        CQ_end rfl rfl rfl) rfl rfl rfl) n))) (CK_block CQ_end))
      (CQ_local (CL_last (CM_one rfl (CE_or (CE_and (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CE_call (CM_call (CE_index (CE_cell h_M) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))))) (CE_table CF_nil)))) fun n => CBs_let fun c_w => CBs_end
      ((CQ_stat (CS_if (CE_bin (CE_un (CE_cell rfl)) CE_num) (CK_block (CQ_local (CL_last (CM_one rfl (CE_table CF_nil))) fun n => CBs_let fun c_p1 => CBs_end
        ((CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_one rfl (CE_cell rfl))))) fun n => CBs_let fun c_i1 => CBs_let fun c_x2 => CBs_end ((CK_block (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_cell rfl) CP_nil) (CL_last (CM_one rfl (CE_bin CE_str (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))))
          CQ_end rfl rfl rfl)) n))
        (CQ_stat (CS_assign (CP_var (wCell_ok rfl) CP_nil) (CL_last (CM_one rfl (CE_bin (CE_cell rfl) (CE_bin CE_str (CE_call (CM_call (CE_index (CE_glob h_table) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl CE_str))))))))))
        CQ_end rfl rfl rfl) rfl rfl rfl) n))) (CK_block CQ_end))
      (CQ_stat (CS_return (CL_last (CM_one rfl (CE_cell rfl))))
      CQ_end rfl rfl rfl) rfl rfl rfl) n)) rfl rfl rfl) n)) rfl rfl rfl) n))) n)

def ids (I : Sem) (env0 : Env) (c_d : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_rows => S.let1 fun c_f => S.letEnd ((S.block (S.qLocal (S.lLast (S.mOne (S.eTable S.fNil))) fun n => S.let1 fun c_p => S.letEnd
      ((S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mOne (S.eCell c_rows))))) fun n => S.let1 fun c_i => S.let1 fun c_x => S.letEnd ((S.block (S.qStat (S.sAssign (S.pIndex I (S.eCell c_p) (S.eCell c_i) S.pNil) (S.lLast (S.mOne (S.eOr (S.eAnd (S.eCell c_f) (S.eFirst (S.mCall I (S.eCell c_f) (S.lLast (S.mOne (S.eCell c_x)))))) (S.eBin I .concat (S.eStr "#".toList) (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eCell c_x)))))))))) (S.gotos [] [])
        S.qEnd)) n)) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lLast (S.mCall I (S.eIndex I (S.eGlob "table") (S.eStr "concat".toList)) (S.lCons (S.eCell c_p) (S.lLast (S.mOne (S.eStr ", ".toList))))))) (S.gotos [] [])
      S.qEnd)) n))) n)

theorem ids_ok (I : Sem) (env0 : Env) (c_d : Nat)
    (h_d : env0.lookup "d" = some c_d)
    (h_ipairs : env0.lookup "ipairs" = none)
    (h_table : env0.lookup "table" = none) :
    CFn I (ids I env0 c_d) ⟨["rows", "f"], false, ids_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_rows => CBs_let fun c_f => CBs_end ((CK_block (CQ_local (CL_last (CM_one rfl (CE_table CF_nil))) fun n => CBs_let fun c_p => CBs_end
      ((CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_one rfl (CE_cell rfl))))) fun n => CBs_let fun c_i => CBs_let fun c_x => CBs_end ((CK_block (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_cell rfl) CP_nil) (CL_last (CM_one rfl (CE_or (CE_and (CE_cell rfl) (CE_call (CM_call (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl)))))) (CE_bin CE_str (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_cell rfl))))))))))
        CQ_end rfl rfl rfl)) n))
      (CQ_stat (CS_return (CL_last (CM_call (CE_index (CE_glob h_table) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl CE_str))))))
      CQ_end rfl rfl rfl) rfl rfl rfl) n))) n)

def no_task_to_wait_on (I : Sem) (env0 : Env) (c_util c_d : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_c => S.let1 fun c_deps => S.letEnd ((S.block (S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mOne (S.eCell c_deps))))) fun n => S.let1 fun c__ => S.let1 fun c_x => S.letEnd ((S.block (S.qStat (S.sIf (S.eUn .not (S.eFirst (S.mMethod I (S.eCell c_c) "one" (S.lCons (S.eStr "select 1 from task where id=?".toList) (S.lLast (S.mOne (S.eCell c_x))))))) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "no task #%s to wait on".toList)) "format" (S.lLast (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eCell c_x))))))))) (S.gotos [] [])
          S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
        S.qEnd)) n)) (S.gotos [] [])
      S.qEnd)) n)

theorem no_task_to_wait_on_ok (I : Sem) (env0 : Env) (c_util c_d : Nat)
    (h_util : env0.lookup "util" = some c_util)
    (h_d : env0.lookup "d" = some c_d)
    (h_ipairs : env0.lookup "ipairs" = none) :
    CFn I (no_task_to_wait_on I env0 c_util c_d) ⟨["c", "deps"], false, no_task_to_wait_on_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_c => CBs_let fun c_deps => CBs_end ((CK_block (CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_one rfl (CE_cell rfl))))) fun n => CBs_let fun c__ => CBs_let fun c_x => CBs_end ((CK_block (CQ_stat (CS_if (CE_un (CE_method (CM_method (CE_cell rfl) (CL_cons CE_str (CL_last (CM_one rfl (CE_cell rfl))))))) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_last (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_cell rfl)))))))))
          CQ_end rfl rfl rfl)) (CK_block CQ_end))
        CQ_end rfl rfl rfl)) n))
      CQ_end rfl rfl rfl)) n)

def M_set_deps (I : Sem) (env0 : Env) (c_no_task_to_wait_on c_M c_d c_util : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_c => S.let1 fun c_id => S.let1 fun c_deps => S.letEnd ((S.block (S.qLocal (S.lLast (S.mOne (S.eTable S.fNil))) fun n => S.let1 fun c_ds => S.letEnd
      ((S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mOne (S.eCell c_deps))))) fun n => S.let1 fun c_i => S.let1 fun c_x => S.letEnd ((S.block (S.qStat (S.sCall (S.mCall I (S.eCell c_no_task_to_wait_on) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eTable (S.fLast (S.mOne (S.eCell c_x))))))))) (S.gotos [] [])
        (S.qLocal (S.lLast (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "dep_path".toList)) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_x) (S.lLast (S.mOne (S.eCell c_id))))))) fun n => S.let1 fun c_cyc => S.letEnd
        ((S.qStat (S.sIf (S.eCell c_cyc) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eGlob "table") (S.eStr "insert".toList)) (S.lCons (S.eCell c_cyc) (S.lCons (S.eNum (.int 1)) (S.lLast (S.mOne (S.eCell c_id))))))) (S.gotos [] [])
          (S.qLocal (S.lLast (S.mOne (S.eTable S.fNil))) fun n => S.let1 fun c_p => S.letEnd
          ((S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mOne (S.eCell c_cyc))))) fun n => S.let1 fun c_j => S.let1 fun c_y => S.letEnd ((S.block (S.qStat (S.sAssign (S.pIndex I (S.eCell c_p) (S.eCell c_j) S.pNil) (S.lLast (S.mOne (S.eBin I .concat (S.eStr "#".toList) (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eCell c_y))))))))) (S.gotos [] [])
            S.qEnd)) n)) (S.gotos [] [])
          (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mOne (S.eBin I .concat (S.eStr "that would be a cycle: ".toList) (S.eFirst (S.mCall I (S.eIndex I (S.eGlob "table") (S.eStr "concat".toList)) (S.lCons (S.eCell c_p) (S.lLast (S.mOne (S.eStr " \xe2\x86\x92 ".toList))))))))))) (S.gotos [] [])
          S.qEnd)) n)))) (S.block S.qEnd)) (S.gotos [] [])
        (S.qStat (S.sAssign (S.pIndex I (S.eCell c_ds) (S.eCell c_i) S.pNil) (S.lLast (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eCell c_x)))))) (S.gotos [] [])
        S.qEnd)) n)))) n)) (S.gotos [] [])
      (S.qStat (S.sCall (S.mMethod I (S.eCell c_c) "exec" (S.lCons (S.eStr "update task set deps=? where id=?".toList) (S.lCons (S.eFirst (S.mCall I (S.eIndex I (S.eGlob "table") (S.eStr "concat".toList)) (S.lCons (S.eCell c_ds) (S.lLast (S.mOne (S.eStr ",".toList)))))) (S.lLast (S.mOne (S.eCell c_id))))))) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lLast (S.mOne (S.eCell c_ds)))) (S.gotos [] [])
      S.qEnd))) n))) n)

theorem M_set_deps_ok (I : Sem) (env0 : Env) (c_no_task_to_wait_on c_M c_d c_util : Nat)
    (h_no_task_to_wait_on : env0.lookup "no_task_to_wait_on" = some c_no_task_to_wait_on)
    (h_M : env0.lookup "M" = some c_M)
    (h_d : env0.lookup "d" = some c_d)
    (h_util : env0.lookup "util" = some c_util)
    (h_ipairs : env0.lookup "ipairs" = none)
    (h_table : env0.lookup "table" = none) :
    CFn I (M_set_deps I env0 c_no_task_to_wait_on c_M c_d c_util) ⟨["c", "id", "deps"], false, M_set_deps_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_c => CBs_let fun c_id => CBs_let fun c_deps => CBs_end ((CK_block (CQ_local (CL_last (CM_one rfl (CE_table CF_nil))) fun n => CBs_let fun c_ds => CBs_end
      ((CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_one rfl (CE_cell rfl))))) fun n => CBs_let fun c_i => CBs_let fun c_x => CBs_end ((CK_block (CQ_stat (CS_call (CM_call (CE_cell h_no_task_to_wait_on) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_table (CF_last (CM_one rfl (CE_cell rfl)))))))))
        (CQ_local (CL_last (CM_call (CE_index (CE_cell h_M) CE_str) (CL_cons (CE_cell rfl) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl))))))) fun n => CBs_let fun c_cyc => CBs_end
        ((CQ_stat (CS_if (CE_cell rfl) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_glob h_table) CE_str) (CL_cons (CE_cell rfl) (CL_cons CE_num (CL_last (CM_one rfl (CE_cell rfl)))))))
          (CQ_local (CL_last (CM_one rfl (CE_table CF_nil))) fun n => CBs_let fun c_p => CBs_end
          ((CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_one rfl (CE_cell rfl))))) fun n => CBs_let fun c_j => CBs_let fun c_y => CBs_end ((CK_block (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_cell rfl) CP_nil) (CL_last (CM_one rfl (CE_bin CE_str (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_cell rfl)))))))))
            CQ_end rfl rfl rfl)) n))
          (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_one rfl (CE_bin CE_str (CE_call (CM_call (CE_index (CE_glob h_table) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl CE_str))))))))))
          CQ_end rfl rfl rfl) rfl rfl rfl) n)) rfl rfl rfl)) (CK_block CQ_end))
        (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_cell rfl) CP_nil) (CL_last (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_cell rfl))))))
        CQ_end rfl rfl rfl) rfl rfl rfl) n)) rfl rfl rfl)) n))
      (CQ_stat (CS_call (CM_method (CE_cell rfl) (CL_cons CE_str (CL_cons (CE_call (CM_call (CE_index (CE_glob h_table) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl CE_str))))) (CL_last (CM_one rfl (CE_cell rfl)))))))
      (CQ_stat (CS_return (CL_last (CM_one rfl (CE_cell rfl))))
      CQ_end rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) n))) n)

def ctx_of (I : Sem) (env0 : Env) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_c => S.let1 fun c_n => S.letEnd ((S.block (S.qLocal (S.lLast (S.mMethod I (S.eCell c_c) "one" (S.lCons (S.eStr "select ctx_tokens from agent where name=?".toList) (S.lLast (S.mOne (S.eCell c_n)))))) fun n => S.let1 fun c_r => S.letEnd
      ((S.qStat (S.sReturn (S.lLast (S.mOne (S.eOr (S.eAnd (S.eCell c_r) (S.eIndex I (S.eCell c_r) (S.eStr "ctx_tokens".toList))) (S.eNum (.int 0)))))) (S.gotos [] [])
      S.qEnd) n))) n)

theorem ctx_of_ok (I : Sem) (env0 : Env) :
    CFn I (ctx_of I env0) ⟨["c", "n"], false, ctx_of_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_c => CBs_let fun c_n => CBs_end ((CK_block (CQ_local (CL_last (CM_method (CE_cell rfl) (CL_cons CE_str (CL_last (CM_one rfl (CE_cell rfl)))))) fun n => CBs_let fun c_r => CBs_end
      ((CQ_stat (CS_return (CL_last (CM_one rfl (CE_or (CE_and (CE_cell rfl) (CE_index (CE_cell rfl) CE_str)) CE_num))))
      CQ_end rfl rfl rfl) n))) n)

def reaped_from (I : Sem) (env0 : Env) (c_M c_d : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_c => S.let1 fun c_n => S.let1 fun c_id => S.letEnd ((S.block (S.qLocal S.lNil fun n => S.let1 fun c_last => S.letEnd
      ((S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "task_events".toList)) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eCell c_id)))))))) fun n => S.let1 fun c__ => S.let1 fun c_e => S.letEnd ((S.block (S.qStat (S.sIf (S.eOr (S.eBin I .eq (S.eIndex I (S.eCell c_e) (S.eStr "kind".toList)) (S.eStr "claim".toList)) (S.eBin I .eq (S.eIndex I (S.eCell c_e) (S.eStr "kind".toList)) (S.eStr "spawn".toList))) (S.block (S.qStat (S.sAssign (S.pVar (S.wCell c_last) S.pNil) (S.lLast (S.mOne (S.eIndex I (S.eCell c_e) (S.eStr "agent".toList))))) (S.gotos [] [])
          S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
        S.qEnd)) n)) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lLast (S.mOne (S.eAnd (S.eBin I .eq (S.eCell c_last) (S.eCell c_n)) (S.eBin I .ne (S.eFirst (S.mMethod I (S.eCell c_c) "one" (S.lCons (S.eStr "select 1 from event where kind='reap' and agent=? and data=?".toList) (S.lCons (S.eCell c_n) (S.lLast (S.mMethod I (S.eParen (S.eStr "task #%s lease expired".toList)) "format" (S.lLast (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eCell c_id))))))))))) S.eNil))))) (S.gotos [] [])
      S.qEnd)) n))) n)

theorem reaped_from_ok (I : Sem) (env0 : Env) (c_M c_d : Nat)
    (h_M : env0.lookup "M" = some c_M)
    (h_d : env0.lookup "d" = some c_d)
    (h_ipairs : env0.lookup "ipairs" = none) :
    CFn I (reaped_from I env0 c_M c_d) ⟨["c", "n", "id"], false, reaped_from_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_c => CBs_let fun c_n => CBs_let fun c_id => CBs_end ((CK_block (CQ_local CL_nil fun n => CBs_let fun c_last => CBs_end
      ((CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_call (CE_index (CE_cell h_M) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl)))))))) fun n => CBs_let fun c__ => CBs_let fun c_e => CBs_end ((CK_block (CQ_stat (CS_if (CE_or (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str)) (CK_block (CQ_stat (CS_assign (CP_var (wCell_ok rfl) CP_nil) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))
          CQ_end rfl rfl rfl)) (CK_block CQ_end))
        CQ_end rfl rfl rfl)) n))
      (CQ_stat (CS_return (CL_last (CM_one rfl (CE_and (CE_bin (CE_cell rfl) (CE_cell rfl)) (CE_bin (CE_method (CM_method (CE_cell rfl) (CL_cons CE_str (CL_cons (CE_cell rfl) (CL_last (CM_method (CE_paren CE_str) (CL_last (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_cell rfl))))))))))) CE_nil)))))
      CQ_end rfl rfl rfl) rfl rfl rfl) n))) n)

def owned (I : Sem) (env0 : Env) (c_py : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_r => S.letEnd ((S.block (S.qStat (S.sReturn (S.lLast (S.mOne (S.eOr (S.eAnd (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "owner".toList)))))) (S.eParen (S.eBin I .concat (S.eStr ", owned by ".toList) (S.eIndex I (S.eCell c_r) (S.eStr "owner".toList))))) (S.eStr "".toList))))) (S.gotos [] [])
      S.qEnd)) n)

theorem owned_ok (I : Sem) (env0 : Env) (c_py : Nat)
    (h_py : env0.lookup "py" = some c_py) :
    CFn I (owned I env0 c_py) ⟨["r"], false, owned_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_r => CBs_end ((CK_block (CQ_stat (CS_return (CL_last (CM_one rfl (CE_or (CE_and (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CE_paren (CE_bin CE_str (CE_index (CE_cell rfl) CE_str)))) CE_str))))
      CQ_end rfl rfl rfl)) n)

def M_cmd_task (I : Sem) (env0 : Env) (c_agents c_util c_no_task_to_wait_on c_d c_py c_db c_M c_ctx_of c_hook c_reaped_from c_owned c_ids : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_c => S.let1 fun c_a => S.letEnd ((S.block (S.qLocal (S.lLast (S.mCall I (S.eIndex I (S.eCell c_agents) (S.eStr "me".toList)) S.lNil)) fun n => S.let1 fun c_n => S.letEnd
      ((S.qLocal (S.lLast (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "now".toList)) S.lNil)) fun n => S.let1 fun c_t => S.letEnd
      ((S.qStat (S.sIf (S.eBin I .eq (S.eIndex I (S.eCell c_a) (S.eStr "act".toList)) (S.eStr "add".toList)) (S.block (S.qLocal (S.lLast (S.mOne (S.eOr (S.eIndex I (S.eCell c_a) (S.eStr "after".toList)) (S.eTable S.fNil)))) fun n => S.let1 fun c_deps => S.letEnd
        ((S.qLocal (S.lLast (S.mMethod I (S.eCell c_c) "tx" (S.lLast (S.mOne (S.eFunc [] false M_cmd_task_fn_body (("deps", c_deps) :: ("t", c_t) :: ("n", c_n) :: ("a", c_a) :: ("c", c_c) :: env0)))))) fun n => S.let1 fun c_id => S.letEnd
        ((S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mOne (S.eBin I .concat (S.eStr "task #".toList) (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eCell c_id)))))))))) (S.gotos [] [])
        (S.qStat (S.sReturn S.lNil) (S.gotos [] [])
        S.qEnd)) n)) n))) (S.block S.qEnd)) (S.gotos [] [])
      (S.qLocal (S.lLast (S.mMethod I (S.eCell c_c) "one" (S.lCons (S.eStr "select * from task where id=?".toList) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList))))))) fun n => S.let1 fun c_r => S.letEnd
      ((S.qStat (S.sIf (S.eUn .not (S.eCell c_r)) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mOne (S.eBin I .concat (S.eStr "no task #".toList) (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList))))))))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qLocal (S.lLast (S.mOne (S.eStr " where id=? and owner=? and state='claimed'".toList))) fun n => S.let1 fun c_mine => S.letEnd
      ((S.qStat (S.sIf (S.eBin I .eq (S.eIndex I (S.eCell c_a) (S.eStr "act".toList)) (S.eStr "claim".toList)) (S.block (S.qLocal (S.lLast (S.mOne (S.eIndex I (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "undone".toList)) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eCell c_r)))))) (S.eNum (.int 1))))) fun n => S.let1 fun c_dep => S.letEnd
        ((S.qStat (S.sIf (S.eCell c_dep) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s waits on #%s (%s%s)".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_dep) (S.eStr "id".toList)))))) (S.lCons (S.eIndex I (S.eCell c_dep) (S.eStr "state".toList)) (S.lLast (S.mOne (S.eOr (S.eAnd (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_dep) (S.eStr "owner".toList)))))) (S.eParen (S.eBin I .concat (S.eStr ", claimed by ".toList) (S.eIndex I (S.eCell c_dep) (S.eStr "owner".toList))))) (S.eStr "".toList))))))))))) (S.gotos [] [])
          S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
        (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_agents) (S.eStr "touch".toList)) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eCell c_n)))))) (S.gotos [] [])
        (S.qLocal (S.lLast (S.mCall I (S.eCell c_ctx_of) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eCell c_n)))))) fun n => S.let1 fun c_k => S.letEnd
        ((S.qStat (S.sIf (S.eAnd (S.eBin I .ge (S.eCell c_k) (S.eIndex I (S.eCell c_hook) (S.eStr "CTX_WARN".toList))) (S.eUn .not (S.eFirst (S.mCall I (S.eCell c_reaped_from) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_n) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))))))) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "context ~%dk, too high to take new work: %s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eIndex I (S.eGlob "math") (S.eStr "floor".toList)) (S.lLast (S.mOne (S.eBin I .div (S.eCell c_k) (S.eNum (.int 1000))))))) (S.lLast (S.mCall I (S.eIndex I (S.eCell c_hook) (S.eStr "ctx_advice".toList)) (S.lLast (S.mOne (S.eCell c_k)))))))))) (S.gotos [] [])
          S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
        (S.qLocal (S.lLast (S.mOne (S.eBin I .add (S.eCell c_t) (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "dur".toList)) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "lease".toList))))))))) fun n => S.let1 fun c_until_ => S.letEnd
        ((S.qStat (S.sIf (S.eBin I .eq (S.eFirst (S.mMethod I (S.eCell c_c) "exec" (S.lCons (S.eBin I .concat (S.eStr "update task set state='claimed', owner=?, lease_until=?, claim_ctx=?, ".toList) (S.eBin I .concat (S.eStr "first_claimed_at=coalesce(first_claimed_at,?) where id=? and state='open' and not exists ".toList) (S.eStr "(select 1 from task d where d.state!='done' and ','||task.deps||',' like '%,'||d.id||',%')".toList))) (S.lCons (S.eCell c_n) (S.lCons (S.eCell c_until_) (S.lCons (S.eCell c_k) (S.lCons (S.eCell c_t) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList))))))))))) (S.eNum (.int 0))) (S.block (S.qLocal (S.lLast (S.mMethod I (S.eCell c_c) "one" (S.lCons (S.eStr "select * from task where id=?".toList) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList))))))) fun n => S.let1 fun c_r2 => S.letEnd
          ((S.qLocal (S.lLast (S.mOne (S.eAnd (S.eBin I .eq (S.eIndex I (S.eCell c_r2) (S.eStr "state".toList)) (S.eStr "open".toList)) (S.eIndex I (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "undone".toList)) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eCell c_r2)))))) (S.eNum (.int 1)))))) fun n => S.let1 fun c_dep2 => S.letEnd
          ((S.qStat (S.sIf (S.eCell c_dep2) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s waits on #%s (%s)".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_dep2) (S.eStr "id".toList)))))) (S.lLast (S.mOne (S.eIndex I (S.eCell c_dep2) (S.eStr "state".toList)))))))))) (S.gotos [] [])
            S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
          (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "task #%s is %s%s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lCons (S.eIndex I (S.eCell c_r2) (S.eStr "state".toList)) (S.lLast (S.mCall I (S.eCell c_owned) (S.lLast (S.mOne (S.eCell c_r2))))))))))) (S.gotos [] [])
          S.qEnd)) n)) n))) (S.block S.qEnd)) (S.gotos [] [])
        (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_db) (S.eStr "log".toList)) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_n) (S.lCons (S.eStr "claim".toList) (S.lCons S.eNil (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s %s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "title".toList))))))))))))) (S.gotos [] [])
        (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mMethod I (S.eParen (S.eStr "claimed #%s until %s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lLast (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "hhmm".toList)) (S.lLast (S.mOne (S.eCell c_until_)))))))))) (S.gotos [] [])
        (S.qLocal (S.lLast (S.mCall I (S.eGlob "require") (S.lLast (S.mOne (S.eStr "swarm.machine".toList))))) fun n => S.let1 fun c_machine => S.letEnd
        ((S.qLocal (S.lLast (S.mCall I (S.eIndex I (S.eCell c_machine) (S.eStr "mem".toList)) S.lNil)) fun n => S.let1 fun c_avail => S.let1 fun c_total => S.let1 fun c_psi => S.letEnd
        ((S.qStat (S.sIf (S.eCell c_avail) (S.block (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mOne (S.eOr (S.eAnd (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_machine) (S.eStr "pressure_high".toList)) (S.lCons (S.eCell c_avail) (S.lCons (S.eCell c_total) (S.lLast (S.mOne (S.eCell c_psi))))))) (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_machine) (S.eStr "machine_note".toList)) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eCell c_n))))))) (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_machine) (S.eStr "machine_line".toList)) (S.lCons (S.eCell c_avail) (S.lCons (S.eCell c_total) (S.lLast (S.mOne (S.eCell c_psi)))))))))))) (S.gotos [] [])
          S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
        (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mOne (S.eOr (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "body".toList)))))) (S.eStr "(no body)".toList)))))) (S.gotos [] [])
        S.qEnd)) n)) n))))) n))) n)))) n))) (S.block (S.qStat (S.sIf (S.eBin I .eq (S.eIndex I (S.eCell c_a) (S.eStr "act".toList)) (S.eStr "show".toList)) (S.block (S.qLocal (S.lLast (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "task_timing".toList)) (S.lCons (S.eCell c_r) (S.lLast (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "task_events".toList)) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "id".toList)))))))))) fun n => S.let1 fun c_tm => S.letEnd
          ((S.qLocalFn "f" ["k"] false f_body (("tm", c_tm) :: ("mine", c_mine) :: ("r", c_r) :: ("t", c_t) :: ("n", c_n) :: ("a", c_a) :: ("c", c_c) :: env0) fun c_f =>
          (S.qLocal (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s %s %s  %s\ntiming: queue %s, work %s, total %s, blocked %s, claims %d, releases %d, held by %s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "id".toList)))))) (S.lCons (S.eIndex I (S.eCell c_r) (S.eStr "state".toList)) (S.lCons (S.eOr (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "owner".toList)))))) (S.eStr "-".toList)) (S.lCons (S.eIndex I (S.eCell c_r) (S.eStr "title".toList)) (S.lCons (S.eFirst (S.mCall I (S.eCell c_f) (S.lLast (S.mOne (S.eStr "queue_wait_s".toList))))) (S.lCons (S.eFirst (S.mCall I (S.eCell c_f) (S.lLast (S.mOne (S.eStr "work_s".toList))))) (S.lCons (S.eFirst (S.mCall I (S.eCell c_f) (S.lLast (S.mOne (S.eStr "total_s".toList))))) (S.lCons (S.eFirst (S.mCall I (S.eCell c_f) (S.lLast (S.mOne (S.eStr "blocked_s".toList))))) (S.lCons (S.eIndex I (S.eCell c_tm) (S.eStr "claims".toList)) (S.lCons (S.eIndex I (S.eCell c_tm) (S.eStr "releases".toList)) (S.lLast (S.mOne (S.eOr (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mCall I (S.eIndex I (S.eGlob "table") (S.eStr "concat".toList)) (S.lCons (S.eIndex I (S.eCell c_tm) (S.eStr "holders".toList)) (S.lLast (S.mOne (S.eStr ", ".toList)))))))) (S.eStr "-".toList)))))))))))))))) fun n => S.let1 fun c_s => S.letEnd
          ((S.qStat (S.sIf (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "base".toList)))))) (S.block (S.qStat (S.sAssign (S.pVar (S.wCell c_s) S.pNil) (S.lLast (S.mOne (S.eBin I .concat (S.eCell c_s) (S.eBin I .concat (S.eStr "\nbase: ".toList) (S.eIndex I (S.eCell c_r) (S.eStr "base".toList))))))) (S.gotos [] [])
            S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
          (S.qStat (S.sIf (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_tm) (S.eStr "claim_ctx".toList)))))) (S.block (S.qStat (S.sAssign (S.pVar (S.wCell c_s) S.pNil) (S.lLast (S.mOne (S.eBin I .concat (S.eCell c_s) (S.eFirst (S.mMethod I (S.eParen (S.eStr ", ctx %dk at claim".toList)) "format" (S.lLast (S.mCall I (S.eIndex I (S.eGlob "math") (S.eStr "floor".toList)) (S.lLast (S.mOne (S.eBin I .div (S.eIndex I (S.eCell c_tm) (S.eStr "claim_ctx".toList)) (S.eNum (.int 1000))))))))))))) (S.gotos [] [])
            S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
          (S.qStat (S.sIf (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_tm) (S.eStr "done_ctx".toList)))))) (S.block (S.qStat (S.sAssign (S.pVar (S.wCell c_s) S.pNil) (S.lLast (S.mOne (S.eBin I .concat (S.eCell c_s) (S.eFirst (S.mMethod I (S.eParen (S.eStr " -> %dk at done".toList)) "format" (S.lLast (S.mCall I (S.eIndex I (S.eGlob "math") (S.eStr "floor".toList)) (S.lLast (S.mOne (S.eBin I .div (S.eIndex I (S.eCell c_tm) (S.eStr "done_ctx".toList)) (S.eNum (.int 1000))))))))))))) (S.gotos [] [])
            S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
          (S.qStat (S.sIf (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_tm) (S.eStr "merged_at".toList)))))) (S.block (S.qStat (S.sAssign (S.pVar (S.wCell c_s) S.pNil) (S.lLast (S.mOne (S.eBin I .concat (S.eCell c_s) (S.eFirst (S.mMethod I (S.eParen (S.eStr "\nPR #%s merged %s, main CI %s".toList)) "format" (S.lCons (S.eOr (S.eAnd (S.eIndex I (S.eCell c_tm) (S.eStr "pr".toList)) (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_tm) (S.eStr "pr".toList))))))) (S.eStr "None".toList)) (S.lCons (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "hhmm".toList)) (S.lLast (S.mOne (S.eIndex I (S.eCell c_tm) (S.eStr "merged_at".toList)))))) (S.lLast (S.mOne (S.eOr (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_tm) (S.eStr "ci_conclusion".toList)))))) (S.eStr "pending".toList)))))))))))) (S.gotos [] [])
            (S.qStat (S.sIf (S.eBin I .ne (S.eIndex I (S.eCell c_tm) (S.eStr "merge_to_green_s".toList)) S.eNil) (S.block (S.qStat (S.sAssign (S.pVar (S.wCell c_s) S.pNil) (S.lLast (S.mOne (S.eBin I .concat (S.eCell c_s) (S.eFirst (S.mMethod I (S.eParen (S.eStr ", green %dm after merge".toList)) "format" (S.lLast (S.mCall I (S.eIndex I (S.eGlob "math") (S.eStr "floor".toList)) (S.lLast (S.mOne (S.eBin I .div (S.eIndex I (S.eCell c_tm) (S.eStr "merge_to_green_s".toList)) (S.eNum (.int 60))))))))))))) (S.gotos [] [])
              S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
            S.qEnd))) (S.block S.qEnd)) (S.gotos [] [])
          (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mOne (S.eBin I .concat (S.eCell c_s) (S.eBin I .concat (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "dep_lines".toList)) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eCell c_r)))))) (S.eBin I .concat (S.eStr "\n".toList) (S.eBin I .concat (S.eParen (S.eOr (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "body".toList)))))) (S.eStr "(no body)".toList))) (S.eParen (S.eOr (S.eAnd (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "answer".toList)))))) (S.eBin I .concat (S.eStr "\nAnswer to the block: ".toList) (S.eIndex I (S.eCell c_r) (S.eStr "answer".toList)))) (S.eStr "".toList))))))))))) (S.gotos [] [])
          S.qEnd))))) n))) n))) (S.block (S.qStat (S.sIf (S.eBin I .eq (S.eIndex I (S.eCell c_a) (S.eStr "act".toList)) (S.eStr "after".toList)) (S.block (S.qStat (S.sCall (S.mMethod I (S.eCell c_c) "tx" (S.lLast (S.mOne (S.eFunc [] false M_cmd_task_fn1_body (("mine", c_mine) :: ("r", c_r) :: ("t", c_t) :: ("n", c_n) :: ("a", c_a) :: ("c", c_c) :: env0)))))) (S.gotos [] [])
            (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s after %s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lLast (S.mOne (S.eOr (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mCall I (S.eCell c_ids) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "deps".toList)))))))) (S.eStr "nothing".toList))))))))) (S.gotos [] [])
            S.qEnd))) (S.block (S.qStat (S.sIf (S.eBin I .eq (S.eIndex I (S.eCell c_a) (S.eStr "act".toList)) (S.eStr "renew".toList)) (S.block (S.qLocal (S.lLast (S.mOne (S.eBin I .add (S.eCell c_t) (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "dur".toList)) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "lease".toList))))))))) fun n => S.let1 fun c_until_1 => S.letEnd
              ((S.qStat (S.sIf (S.eBin I .eq (S.eFirst (S.mMethod I (S.eCell c_c) "exec" (S.lCons (S.eBin I .concat (S.eStr "update task set lease_until=?".toList) (S.eCell c_mine)) (S.lCons (S.eCell c_until_1) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)) (S.lLast (S.mOne (S.eCell c_n)))))))) (S.eNum (.int 0))) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "task #%s is not claimed by you".toList)) "format" (S.lLast (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))))))) (S.gotos [] [])
                S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
              (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mMethod I (S.eParen (S.eStr "renewed #%s until %s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lLast (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "hhmm".toList)) (S.lLast (S.mOne (S.eCell c_until_1)))))))))) (S.gotos [] [])
              S.qEnd)) n))) (S.block (S.qStat (S.sIf (S.eBin I .eq (S.eIndex I (S.eCell c_a) (S.eStr "act".toList)) (S.eStr "done".toList)) (S.block (S.qStat (S.sIf (S.eBin I .eq (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "strip".toList)) (S.lLast (S.mOne (S.eOr (S.eIndex I (S.eCell c_a) (S.eStr "evidence".toList)) (S.eStr "".toList)))))) (S.eStr "".toList)) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mOne (S.eStr "--evidence is empty: give the sha, PR or command output that shows the work is done".toList))))) (S.gotos [] [])
                  S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
                (S.qStat (S.sIf (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "startswith".toList)) (S.lCons (S.eOr (S.eIndex I (S.eCell c_r) (S.eStr "title".toList)) (S.eStr "".toList)) (S.lLast (S.mOne (S.eIndex I (S.eCell c_M) (S.eStr "RED_TASK".toList))))))) (S.block (S.qStat (S.sIf (S.eBin I .eq (S.eFirst (S.mMethod I (S.eCell c_c) "exec" (S.lCons (S.eBin I .concat (S.eStr "update task set evidence=?".toList) (S.eCell c_mine)) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "evidence".toList)) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)) (S.lLast (S.mOne (S.eCell c_n)))))))) (S.eNum (.int 0))) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "task #%s is not claimed by you".toList)) "format" (S.lLast (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))))))) (S.gotos [] [])
                    S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
                  (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s stays yours until a green run: watchd marks it done then, and you can go idle now.".toList)) "format" (S.lLast (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))))))) (S.gotos [] [])
                  (S.qStat (S.sReturn S.lNil) (S.gotos [] [])
                  S.qEnd)))) (S.block S.qEnd)) (S.gotos [] [])
                (S.qStat (S.sCall (S.mMethod I (S.eCell c_c) "tx" (S.lLast (S.mOne (S.eFunc [] false M_cmd_task_fn2_body (("mine", c_mine) :: ("r", c_r) :: ("t", c_t) :: ("n", c_n) :: ("a", c_a) :: ("c", c_c) :: env0)))))) (S.gotos [] [])
                (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mOne (S.eBin I .concat (S.eStr "done #".toList) (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList))))))))))) (S.gotos [] [])
                (S.qLocal (S.lCons (S.eFirst (S.mCall I (S.eIndex I (S.eGlob "math") (S.eStr "floor".toList)) (S.lLast (S.mOne (S.eBin I .div (S.eFirst (S.mCall I (S.eCell c_ctx_of) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eCell c_n)))))) (S.eNum (.int 1000))))))) (S.lLast (S.mCall I (S.eIndex I (S.eCell c_agents) (S.eStr "stay_of".toList)) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eCell c_n))))))) fun n => S.let1 fun c_k1 => S.let1 fun c_stay => S.letEnd
                ((S.qStat (S.sIf (S.eCell c_stay) (S.block (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mMethod I (S.eParen (S.eStr "context ~%dk: you stay for '%s'. `swarm stay --end` when that is over.".toList)) "format" (S.lCons (S.eCell c_k1) (S.lLast (S.mOne (S.eCell c_stay)))))))) (S.gotos [] [])
                  S.qEnd)) (S.block (S.qStat (S.sIf (S.eAnd (S.eBin I .lt (S.eBin I .mul (S.eCell c_k1) (S.eNum (.int 1000))) (S.eIndex I (S.eCell c_agents) (S.eStr "SMALL_CTX".toList))) (S.eBin I .gt (S.eUn .len (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "pool".toList)) (S.lLast (S.mOne (S.eCell c_c)))))) (S.eNum (.int 0)))) (S.block (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mMethod I (S.eParen (S.eStr "context ~%dk: take the next task (swarm board).".toList)) "format" (S.lLast (S.mOne (S.eCell c_k1))))))) (S.gotos [] [])
                    S.qEnd)) (S.block (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mMethod I (S.eParen (S.eStr "context ~%dk: go idle. watchd ends you once your work lands; a fresh agent takes new work.".toList)) "format" (S.lLast (S.mOne (S.eCell c_k1))))))) (S.gotos [] [])
                    S.qEnd))) (S.gotos [] [])
                  S.qEnd))) (S.gotos [] [])
                S.qEnd) n))))))) (S.block (S.qStat (S.sIf (S.eBin I .eq (S.eIndex I (S.eCell c_a) (S.eStr "act".toList)) (S.eStr "block".toList)) (S.block (S.qStat (S.sCall (S.mMethod I (S.eCell c_c) "tx" (S.lLast (S.mOne (S.eFunc [] false M_cmd_task_fn3_body (("mine", c_mine) :: ("r", c_r) :: ("t", c_t) :: ("n", c_n) :: ("a", c_a) :: ("c", c_c) :: env0)))))) (S.gotos [] [])
                  (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mMethod I (S.eParen (S.eStr "blocked #%s; watchd tells the communicator. It stays yours until `swarm task unblock`.".toList)) "format" (S.lLast (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))))))) (S.gotos [] [])
                  S.qEnd))) (S.block (S.qStat (S.sIf (S.eBin I .eq (S.eIndex I (S.eCell c_a) (S.eStr "act".toList)) (S.eStr "unblock".toList)) (S.block (S.qStat (S.sIf (S.eBin I .ne (S.eIndex I (S.eCell c_r) (S.eStr "state".toList)) (S.eStr "blocked".toList)) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "task #%s is not blocked".toList)) "format" (S.lLast (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))))))) (S.gotos [] [])
                      S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
                    (S.qStat (S.sIf (S.eAnd (S.eBin I .ne (S.eCell c_n) (S.eIndex I (S.eCell c_r) (S.eStr "owner".toList))) (S.eUn .not (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_agents) (S.eStr "is_comms".toList)) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eCell c_n)))))))) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "only %s or the communicator can unblock #%s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eGlob "tostring") (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "owner".toList)))))) (S.lLast (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList))))))))))) (S.gotos [] [])
                      S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
                    (S.qStat (S.sCall (S.mMethod I (S.eCell c_c) "tx" (S.lLast (S.mOne (S.eFunc [] false M_cmd_task_fn4_body (("mine", c_mine) :: ("r", c_r) :: ("t", c_t) :: ("n", c_n) :: ("a", c_a) :: ("c", c_c) :: env0)))))) (S.gotos [] [])
                    (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mMethod I (S.eParen (S.eStr "unblocked #%s; claimed by %s again".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "owner".toList))))))))) (S.gotos [] [])
                    S.qEnd))))) (S.block (S.qStat (S.sIf (S.eBin I .eq (S.eIndex I (S.eCell c_a) (S.eStr "act".toList)) (S.eStr "release".toList)) (S.block (S.qStat (S.sCall (S.mMethod I (S.eCell c_c) "tx" (S.lLast (S.mOne (S.eFunc [] false M_cmd_task_fn5_body (("mine", c_mine) :: ("r", c_r) :: ("t", c_t) :: ("n", c_n) :: ("a", c_a) :: ("c", c_c) :: env0)))))) (S.gotos [] [])
                      (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mMethod I (S.eParen (S.eStr "released #%s; it is open again%s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lLast (S.mOne (S.eOr (S.eAnd (S.eAnd (S.eIndex I (S.eCell c_a) (S.eStr "after".toList)) (S.eBin I .gt (S.eUn .len (S.eIndex I (S.eCell c_a) (S.eStr "after".toList))) (S.eNum (.int 0)))) (S.eParen (S.eBin I .concat (S.eStr " after ".toList) (S.eFirst (S.mCall I (S.eCell c_ids) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "after".toList))))))))) (S.eStr "".toList))))))))) (S.gotos [] [])
                      S.qEnd))) (S.block (S.qStat (S.sIf (S.eBin I .eq (S.eIndex I (S.eCell c_a) (S.eStr "act".toList)) (S.eStr "drop".toList)) (S.block (S.qStat (S.sCall (S.mMethod I (S.eCell c_c) "tx" (S.lLast (S.mOne (S.eFunc [] false M_cmd_task_fn6_body (("mine", c_mine) :: ("r", c_r) :: ("t", c_t) :: ("n", c_n) :: ("a", c_a) :: ("c", c_c) :: env0)))))) (S.gotos [] [])
                        (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mOne (S.eBin I .concat (S.eStr "dropped #".toList) (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList))))))))))) (S.gotos [] [])
                        (S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "waiters".toList)) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList))))))))) fun n => S.let1 fun c__ => S.let1 fun c_w => S.letEnd ((S.block (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s waits on #%s: drop it too, or `swarm task after %s \xe2\x80\xa6`".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_w) (S.eStr "id".toList)))))) (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lLast (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_w) (S.eStr "id".toList)))))))))))) (S.gotos [] [])
                          S.qEnd)) n)) (S.gotos [] [])
                        S.qEnd)))) (S.block S.qEnd)) (S.gotos [] [])
                      S.qEnd))) (S.gotos [] [])
                    S.qEnd))) (S.gotos [] [])
                  S.qEnd))) (S.gotos [] [])
                S.qEnd))) (S.gotos [] [])
              S.qEnd))) (S.gotos [] [])
            S.qEnd))) (S.gotos [] [])
          S.qEnd))) (S.gotos [] [])
        S.qEnd))) (S.gotos [] [])
      S.qEnd) n))) n))) n)) n))) n)

theorem M_cmd_task_ok (I : Sem) (env0 : Env) (c_agents c_util c_no_task_to_wait_on c_d c_py c_db c_M c_ctx_of c_hook c_reaped_from c_owned c_ids : Nat)
    (h_agents : env0.lookup "agents" = some c_agents)
    (h_util : env0.lookup "util" = some c_util)
    (h_no_task_to_wait_on : env0.lookup "no_task_to_wait_on" = some c_no_task_to_wait_on)
    (h_d : env0.lookup "d" = some c_d)
    (h_py : env0.lookup "py" = some c_py)
    (h_db : env0.lookup "db" = some c_db)
    (h_M : env0.lookup "M" = some c_M)
    (h_ctx_of : env0.lookup "ctx_of" = some c_ctx_of)
    (h_hook : env0.lookup "hook" = some c_hook)
    (h_reaped_from : env0.lookup "reaped_from" = some c_reaped_from)
    (h_owned : env0.lookup "owned" = some c_owned)
    (h_ids : env0.lookup "ids" = some c_ids)
    (h_ipairs : env0.lookup "ipairs" = none)
    (h_table : env0.lookup "table" = none)
    (h_print : env0.lookup "print" = none)
    (h_math : env0.lookup "math" = none)
    (h_require : env0.lookup "require" = none)
    (h_tostring : env0.lookup "tostring" = none) :
    CFn I (M_cmd_task I env0 c_agents c_util c_no_task_to_wait_on c_d c_py c_db c_M c_ctx_of c_hook c_reaped_from c_owned c_ids) ⟨["c", "a"], false, M_cmd_task_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_c => CBs_let fun c_a => CBs_end ((CK_block (CQ_local (CL_last (CM_call (CE_index (CE_cell h_agents) CE_str) CL_nil)) fun n => CBs_let fun c_n => CBs_end
      ((CQ_local (CL_last (CM_call (CE_index (CE_cell h_util) CE_str) CL_nil)) fun n => CBs_let fun c_t => CBs_end
      ((CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_local (CL_last (CM_one rfl (CE_or (CE_index (CE_cell rfl) CE_str) (CE_table CF_nil)))) fun n => CBs_let fun c_deps => CBs_end
        ((CQ_local (CL_last (CM_method (CE_cell rfl) (CL_last (CM_one rfl (CE_func (by rfl)))))) fun n => CBs_let fun c_id => CBs_end
        ((CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_one rfl (CE_bin CE_str (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_cell rfl))))))))))
        (CQ_stat (CS_return CL_nil)
        CQ_end rfl rfl rfl) rfl rfl rfl) n)) n))) (CK_block CQ_end))
      (CQ_local (CL_last (CM_method (CE_cell rfl) (CL_cons CE_str (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))) fun n => CBs_let fun c_r => CBs_end
      ((CQ_stat (CS_if (CE_un (CE_cell rfl)) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_one rfl (CE_bin CE_str (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))))))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_local (CL_last (CM_one rfl CE_str)) fun n => CBs_let fun c_mine => CBs_end
      ((CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_local (CL_last (CM_one rfl (CE_index (CE_call (CM_call (CE_index (CE_cell h_M) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl)))))) CE_num))) fun n => CBs_let fun c_dep => CBs_end
        ((CQ_stat (CS_if (CE_cell rfl) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_last (CM_one rfl (CE_or (CE_and (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CE_paren (CE_bin CE_str (CE_index (CE_cell rfl) CE_str)))) CE_str))))))))))
          CQ_end rfl rfl rfl)) (CK_block CQ_end))
        (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_agents) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl))))))
        (CQ_local (CL_last (CM_call (CE_cell h_ctx_of) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl)))))) fun n => CBs_let fun c_k => CBs_end
        ((CQ_stat (CS_if (CE_and (CE_bin (CE_cell rfl) (CE_index (CE_cell h_hook) CE_str)) (CE_un (CE_call (CM_call (CE_cell h_reaped_from) (CL_cons (CE_cell rfl) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))))))) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_index (CE_glob h_math) CE_str) (CL_last (CM_one rfl (CE_bin (CE_cell rfl) CE_num))))) (CL_last (CM_call (CE_index (CE_cell h_hook) CE_str) (CL_last (CM_one rfl (CE_cell rfl))))))))))
          CQ_end rfl rfl rfl)) (CK_block CQ_end))
        (CQ_local (CL_last (CM_one rfl (CE_bin (CE_cell rfl) (CE_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))) fun n => CBs_let fun c_until_ => CBs_end
        ((CQ_stat (CS_if (CE_bin (CE_method (CM_method (CE_cell rfl) (CL_cons (CE_bin CE_str (CE_bin CE_str CE_str)) (CL_cons (CE_cell rfl) (CL_cons (CE_cell rfl) (CL_cons (CE_cell rfl) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))))) CE_num) (CK_block (CQ_local (CL_last (CM_method (CE_cell rfl) (CL_cons CE_str (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))) fun n => CBs_let fun c_r2 => CBs_end
          ((CQ_local (CL_last (CM_one rfl (CE_and (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CE_index (CE_call (CM_call (CE_index (CE_cell h_M) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl)))))) CE_num)))) fun n => CBs_let fun c_dep2 => CBs_end
          ((CQ_stat (CS_if (CE_cell rfl) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))))
            CQ_end rfl rfl rfl)) (CK_block CQ_end))
          (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_last (CM_call (CE_cell h_owned) (CL_last (CM_one rfl (CE_cell rfl)))))))))))
          CQ_end rfl rfl rfl) rfl rfl rfl) n)) n))) (CK_block CQ_end))
        (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_db) CE_str) (CL_cons (CE_cell rfl) (CL_cons (CE_cell rfl) (CL_cons CE_str (CL_cons CE_nil (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))))))))))
        (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_last (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_one rfl (CE_cell rfl))))))))))
        (CQ_local (CL_last (CM_call (CE_glob h_require) (CL_last (CM_one rfl CE_str)))) fun n => CBs_let fun c_machine => CBs_end
        ((CQ_local (CL_last (CM_call (CE_index (CE_cell rfl) CE_str) CL_nil)) fun n => CBs_let fun c_avail => CBs_let fun c_total => CBs_let fun c_psi => CBs_end
        ((CQ_stat (CS_if (CE_cell rfl) (CK_block (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_one rfl (CE_or (CE_and (CE_call (CM_call (CE_index (CE_cell rfl) CE_str) (CL_cons (CE_cell rfl) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl))))))) (CE_call (CM_call (CE_index (CE_cell rfl) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl))))))) (CE_call (CM_call (CE_index (CE_cell rfl) CE_str) (CL_cons (CE_cell rfl) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl))))))))))))
          CQ_end rfl rfl rfl)) (CK_block CQ_end))
        (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_one rfl (CE_or (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) CE_str)))))
        CQ_end rfl rfl rfl) rfl rfl rfl) n)) n)) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) n)) rfl rfl rfl) n)) rfl rfl rfl) rfl rfl rfl) n))) (CK_block (CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_local (CL_last (CM_call (CE_index (CE_cell h_M) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_call (CE_index (CE_cell h_M) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))))))) fun n => CBs_let fun c_tm => CBs_end
          ((CQ_localFn (by rfl) fun c_f =>
          (CQ_local (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_cons (CE_or (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) CE_str) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_cons (CE_call (CM_call (CE_cell rfl) (CL_last (CM_one rfl CE_str)))) (CL_cons (CE_call (CM_call (CE_cell rfl) (CL_last (CM_one rfl CE_str)))) (CL_cons (CE_call (CM_call (CE_cell rfl) (CL_last (CM_one rfl CE_str)))) (CL_cons (CE_call (CM_call (CE_cell rfl) (CL_last (CM_one rfl CE_str)))) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_last (CM_one rfl (CE_or (CE_call (CM_call (CE_cell h_py) (CL_last (CM_call (CE_index (CE_glob h_table) CE_str) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_last (CM_one rfl CE_str))))))) CE_str))))))))))))))) fun n => CBs_let fun c_s => CBs_end
          ((CQ_stat (CS_if (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CK_block (CQ_stat (CS_assign (CP_var (wCell_ok rfl) CP_nil) (CL_last (CM_one rfl (CE_bin (CE_cell rfl) (CE_bin CE_str (CE_index (CE_cell rfl) CE_str))))))
            CQ_end rfl rfl rfl)) (CK_block CQ_end))
          (CQ_stat (CS_if (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CK_block (CQ_stat (CS_assign (CP_var (wCell_ok rfl) CP_nil) (CL_last (CM_one rfl (CE_bin (CE_cell rfl) (CE_method (CM_method (CE_paren CE_str) (CL_last (CM_call (CE_index (CE_glob h_math) CE_str) (CL_last (CM_one rfl (CE_bin (CE_index (CE_cell rfl) CE_str) CE_num)))))))))))
            CQ_end rfl rfl rfl)) (CK_block CQ_end))
          (CQ_stat (CS_if (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CK_block (CQ_stat (CS_assign (CP_var (wCell_ok rfl) CP_nil) (CL_last (CM_one rfl (CE_bin (CE_cell rfl) (CE_method (CM_method (CE_paren CE_str) (CL_last (CM_call (CE_index (CE_glob h_math) CE_str) (CL_last (CM_one rfl (CE_bin (CE_index (CE_cell rfl) CE_str) CE_num)))))))))))
            CQ_end rfl rfl rfl)) (CK_block CQ_end))
          (CQ_stat (CS_if (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CK_block (CQ_stat (CS_assign (CP_var (wCell_ok rfl) CP_nil) (CL_last (CM_one rfl (CE_bin (CE_cell rfl) (CE_method (CM_method (CE_paren CE_str) (CL_cons (CE_or (CE_and (CE_index (CE_cell rfl) CE_str) (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))) CE_str) (CL_cons (CE_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_last (CM_one rfl (CE_or (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) CE_str)))))))))))
            (CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_nil) (CK_block (CQ_stat (CS_assign (CP_var (wCell_ok rfl) CP_nil) (CL_last (CM_one rfl (CE_bin (CE_cell rfl) (CE_method (CM_method (CE_paren CE_str) (CL_last (CM_call (CE_index (CE_glob h_math) CE_str) (CL_last (CM_one rfl (CE_bin (CE_index (CE_cell rfl) CE_str) CE_num)))))))))))
              CQ_end rfl rfl rfl)) (CK_block CQ_end))
            CQ_end rfl rfl rfl) rfl rfl rfl)) (CK_block CQ_end))
          (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_one rfl (CE_bin (CE_cell rfl) (CE_bin (CE_call (CM_call (CE_index (CE_cell h_M) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl)))))) (CE_bin CE_str (CE_bin (CE_paren (CE_or (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) CE_str)) (CE_paren (CE_or (CE_and (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CE_bin CE_str (CE_index (CE_cell rfl) CE_str))) CE_str))))))))))
          CQ_end rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) n))) n))) (CK_block (CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_stat (CS_call (CM_method (CE_cell rfl) (CL_last (CM_one rfl (CE_func (by rfl))))))
            (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_last (CM_one rfl (CE_or (CE_call (CM_call (CE_cell h_py) (CL_last (CM_call (CE_cell h_ids) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))))) CE_str))))))))
            CQ_end rfl rfl rfl) rfl rfl rfl)) (CK_block (CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_local (CL_last (CM_one rfl (CE_bin (CE_cell rfl) (CE_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))) fun n => CBs_let fun c_until_1 => CBs_end
              ((CQ_stat (CS_if (CE_bin (CE_method (CM_method (CE_cell rfl) (CL_cons (CE_bin CE_str (CE_cell rfl)) (CL_cons (CE_cell rfl) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_last (CM_one rfl (CE_cell rfl)))))))) CE_num) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_last (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))))
                CQ_end rfl rfl rfl)) (CK_block CQ_end))
              (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_last (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_one rfl (CE_cell rfl))))))))))
              CQ_end rfl rfl rfl) rfl rfl rfl) n))) (CK_block (CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_stat (CS_if (CE_bin (CE_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_one rfl (CE_or (CE_index (CE_cell rfl) CE_str) CE_str))))) CE_str) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_one rfl CE_str))))
                  CQ_end rfl rfl rfl)) (CK_block CQ_end))
                (CQ_stat (CS_if (CE_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_cons (CE_or (CE_index (CE_cell rfl) CE_str) CE_str) (CL_last (CM_one rfl (CE_index (CE_cell h_M) CE_str)))))) (CK_block (CQ_stat (CS_if (CE_bin (CE_method (CM_method (CE_cell rfl) (CL_cons (CE_bin CE_str (CE_cell rfl)) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_last (CM_one rfl (CE_cell rfl)))))))) CE_num) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_last (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))))
                    CQ_end rfl rfl rfl)) (CK_block CQ_end))
                  (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_method (CE_paren CE_str) (CL_last (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))))
                  (CQ_stat (CS_return CL_nil)
                  CQ_end rfl rfl rfl) rfl rfl rfl) rfl rfl rfl)) (CK_block CQ_end))
                (CQ_stat (CS_call (CM_method (CE_cell rfl) (CL_last (CM_one rfl (CE_func (by rfl))))))
                (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_one rfl (CE_bin CE_str (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))))))))
                (CQ_local (CL_cons (CE_call (CM_call (CE_index (CE_glob h_math) CE_str) (CL_last (CM_one rfl (CE_bin (CE_call (CM_call (CE_cell h_ctx_of) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl)))))) CE_num))))) (CL_last (CM_call (CE_index (CE_cell h_agents) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl))))))) fun n => CBs_let fun c_k1 => CBs_let fun c_stay => CBs_end
                ((CQ_stat (CS_if (CE_cell rfl) (CK_block (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl))))))))
                  CQ_end rfl rfl rfl)) (CK_block (CQ_stat (CS_if (CE_and (CE_bin (CE_bin (CE_cell rfl) CE_num) (CE_index (CE_cell h_agents) CE_str)) (CE_bin (CE_un (CE_call (CM_call (CE_index (CE_cell h_M) CE_str) (CL_last (CM_one rfl (CE_cell rfl)))))) CE_num)) (CK_block (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_method (CE_paren CE_str) (CL_last (CM_one rfl (CE_cell rfl)))))))
                    CQ_end rfl rfl rfl)) (CK_block (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_method (CE_paren CE_str) (CL_last (CM_one rfl (CE_cell rfl)))))))
                    CQ_end rfl rfl rfl)))
                  CQ_end rfl rfl rfl)))
                CQ_end rfl rfl rfl) n)) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl)) (CK_block (CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_stat (CS_call (CM_method (CE_cell rfl) (CL_last (CM_one rfl (CE_func (by rfl))))))
                  (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_method (CE_paren CE_str) (CL_last (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))))
                  CQ_end rfl rfl rfl) rfl rfl rfl)) (CK_block (CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_last (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))))
                      CQ_end rfl rfl rfl)) (CK_block CQ_end))
                    (CQ_stat (CS_if (CE_and (CE_bin (CE_cell rfl) (CE_index (CE_cell rfl) CE_str)) (CE_un (CE_call (CM_call (CE_index (CE_cell h_agents) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl)))))))) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_glob h_tostring) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_last (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))))))))
                      CQ_end rfl rfl rfl)) (CK_block CQ_end))
                    (CQ_stat (CS_call (CM_method (CE_cell rfl) (CL_last (CM_one rfl (CE_func (by rfl))))))
                    (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))))))
                    CQ_end rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl)) (CK_block (CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_stat (CS_call (CM_method (CE_cell rfl) (CL_last (CM_one rfl (CE_func (by rfl))))))
                      (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_last (CM_one rfl (CE_or (CE_and (CE_and (CE_index (CE_cell rfl) CE_str) (CE_bin (CE_un (CE_index (CE_cell rfl) CE_str)) CE_num)) (CE_paren (CE_bin CE_str (CE_call (CM_call (CE_cell h_ids) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))) CE_str))))))))
                      CQ_end rfl rfl rfl) rfl rfl rfl)) (CK_block (CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_stat (CS_call (CM_method (CE_cell rfl) (CL_last (CM_one rfl (CE_func (by rfl))))))
                        (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_one rfl (CE_bin CE_str (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))))))))
                        (CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_call (CE_index (CE_cell h_M) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))) fun n => CBs_let fun c__ => CBs_let fun c_w => CBs_end ((CK_block (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_last (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))))))
                          CQ_end rfl rfl rfl)) n))
                        CQ_end rfl rfl rfl) rfl rfl rfl) rfl rfl rfl)) (CK_block CQ_end))
                      CQ_end rfl rfl rfl)))
                    CQ_end rfl rfl rfl)))
                  CQ_end rfl rfl rfl)))
                CQ_end rfl rfl rfl)))
              CQ_end rfl rfl rfl)))
            CQ_end rfl rfl rfl)))
          CQ_end rfl rfl rfl)))
        CQ_end rfl rfl rfl)))
      CQ_end rfl rfl rfl) n)) rfl rfl rfl) n)) rfl rfl rfl) n)) n))) n)

def M_cmd_board (I : Sem) (env0 : Env) (c_M c_agents c_py c_d c_util c_ids : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_c => S.let1 fun c_a => S.letEnd ((S.block (S.qLocal (S.lLast (S.mCall I (S.eGlob "require") (S.lLast (S.mOne (S.eStr "swarm.machine".toList))))) fun n => S.let1 fun c_machine => S.letEnd
      ((S.qLocal (S.lLast (S.mCall I (S.eIndex I (S.eCell c_machine) (S.eStr "mem".toList)) S.lNil)) fun n => S.let1 fun c_avail => S.let1 fun c_total => S.let1 fun c_psi => S.letEnd
      ((S.qStat (S.sIf (S.eCell c_avail) (S.block (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mCall I (S.eIndex I (S.eCell c_machine) (S.eStr "machine_line".toList)) (S.lCons (S.eCell c_avail) (S.lCons (S.eCell c_total) (S.lLast (S.mOne (S.eCell c_psi))))))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qLocal (S.lLast (S.mOne (S.eTable S.fNil))) fun n => S.let1 fun c_role => S.letEnd
      ((S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mMethod I (S.eCell c_c) "all" (S.lLast (S.mOne (S.eStr "select name, role from agent where ended is null and role is not null".toList))))))) fun n => S.let1 fun c__ => S.let1 fun c_x => S.letEnd ((S.block (S.qStat (S.sAssign (S.pIndex I (S.eCell c_role) (S.eIndex I (S.eCell c_x) (S.eStr "name".toList)) S.pNil) (S.lLast (S.mOne (S.eIndex I (S.eCell c_x) (S.eStr "role".toList))))) (S.gotos [] [])
        S.qEnd)) n)) (S.gotos [] [])
      (S.qLocal (S.lLast (S.mMethod I (S.eCell c_c) "all" (S.lLast (S.mOne (S.eBin I .concat (S.eStr "select * from task ".toList) (S.eBin I .concat (S.eParen (S.eOr (S.eAnd (S.eIndex I (S.eCell c_a) (S.eStr "all".toList)) (S.eStr "".toList)) (S.eStr "where state in ('open','claimed','blocked') ".toList))) (S.eBin I .concat (S.eStr "order by title like '".toList) (S.eBin I .concat (S.eIndex I (S.eCell c_M) (S.eStr "RED_TASK".toList)) (S.eStr "%' and state!='done' desc, id".toList))))))))) fun n => S.let1 fun c_rows => S.letEnd
      ((S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mCall I (S.eIndex I (S.eCell c_agents) (S.eStr "limits_line".toList)) (S.lLast (S.mOne (S.eCell c_c))))))) (S.gotos [] [])
      (S.qLocal (S.lLast (S.mMethod I (S.eCell c_c) "one" (S.lLast (S.mOne (S.eStr "select v from meta where k='spawn_held'".toList))))) fun n => S.let1 fun c_held => S.letEnd
      ((S.qStat (S.sIf (S.eCell c_held) (S.block (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mOne (S.eIndex I (S.eCell c_held) (S.eStr "v".toList)))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mOne (S.eCell c_rows))))) fun n => S.let1 fun c__1 => S.let1 fun c_r => S.letEnd ((S.block (S.qLocal (S.lLast (S.mOne (S.eBin I .concat (S.eParen (S.eOr (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "owner".toList)))))) (S.eStr "-".toList))) (S.eParen (S.eOr (S.eAnd (S.eIndex I (S.eCell c_role) (S.eIndex I (S.eCell c_r) (S.eStr "owner".toList))) (S.eParen (S.eBin I .concat (S.eStr " (".toList) (S.eBin I .concat (S.eIndex I (S.eCell c_role) (S.eIndex I (S.eCell c_r) (S.eStr "owner".toList))) (S.eStr ")".toList))))) (S.eStr "".toList)))))) fun n => S.let1 fun c_who => S.letEnd
        ((S.qStat (S.sIf (S.eBin I .eq (S.eIndex I (S.eCell c_r) (S.eStr "state".toList)) (S.eStr "blocked".toList)) (S.block (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s blocked by %s: %s  %s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "id".toList)))))) (S.lCons (S.eCell c_who) (S.lCons (S.eOr (S.eIndex I (S.eCell c_r) (S.eStr "question".toList)) (S.eStr "None".toList)) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "title".toList))))))))))) (S.gotos [] [])
          S.qEnd)) (S.block (S.qLocal (S.lLast (S.mOne (S.eStr "".toList))) fun n => S.let1 fun c_lease => S.letEnd
          ((S.qStat (S.sIf (S.eBin I .eq (S.eIndex I (S.eCell c_r) (S.eStr "state".toList)) (S.eStr "claimed".toList)) (S.block (S.qLocal (S.lLast (S.mOne (S.eBin I .sub (S.eParen (S.eOr (S.eIndex I (S.eCell c_r) (S.eStr "lease_until".toList)) (S.eNum (.int 0)))) (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "now".toList)) S.lNil))))) fun n => S.let1 fun c_left => S.letEnd
            ((S.qStat (S.sAssign (S.pVar (S.wCell c_lease) S.pNil) (S.lLast (S.mOne (S.eOr (S.eAnd (S.eBin I .gt (S.eCell c_left) (S.eNum (.int 0))) (S.eFirst (S.mMethod I (S.eParen (S.eStr " lease %dm left".toList)) "format" (S.lLast (S.mCall I (S.eIndex I (S.eGlob "math") (S.eStr "floor".toList)) (S.lLast (S.mOne (S.eBin I .div (S.eCell c_left) (S.eNum (.int 60)))))))))) (S.eStr " lease EXPIRED".toList))))) (S.gotos [] [])
            S.qEnd) n))) (S.block S.qEnd)) (S.gotos [] [])
          (S.qLocal (S.lLast (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "undone".toList)) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eCell c_r)))))) fun n => S.let1 fun c_u => S.letEnd
          ((S.qLocal (S.lLast (S.mOne (S.eOr (S.eAnd (S.eBin I .gt (S.eUn .len (S.eCell c_u)) (S.eNum (.int 0))) (S.eParen (S.eBin I .concat (S.eStr " after ".toList) (S.eFirst (S.mCall I (S.eCell c_ids) (S.lCons (S.eCell c_u) (S.lLast (S.mOne (S.eFunc ["x"] false M_cmd_board_fn_body (("u", c_u) :: ("lease", c_lease) :: ("who", c_who) :: ("r", c_r) :: ("_", c__1) :: ("held", c_held) :: ("rows", c_rows) :: ("role", c_role) :: ("psi", c_psi) :: ("total", c_total) :: ("avail", c_avail) :: ("machine", c_machine) :: ("a", c_a) :: ("c", c_c) :: env0)))))))))) (S.eStr "".toList)))) fun n => S.let1 fun c_wait => S.letEnd
          ((S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mOne (S.eBin I .concat (S.eFirst (S.mMethod I (S.eParen (S.eStr "#%s %-7s %s%s%s  %s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "id".toList)))))) (S.lCons (S.eIndex I (S.eCell c_r) (S.eStr "state".toList)) (S.lCons (S.eCell c_who) (S.lCons (S.eCell c_lease) (S.lCons (S.eCell c_wait) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "title".toList))))))))))) (S.eBin I .concat (S.eParen (S.eOr (S.eAnd (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "body".toList)))))) (S.eStr "  [body: task show]".toList)) (S.eStr "".toList))) (S.eParen (S.eOr (S.eAnd (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "evidence".toList)))))) (S.eParen (S.eBin I .concat (S.eStr "  [evidence: ".toList) (S.eBin I .concat (S.eIndex I (S.eCell c_r) (S.eStr "evidence".toList)) (S.eStr "]".toList))))) (S.eStr "".toList))))))))) (S.gotos [] [])
          S.qEnd) n)) n))) n)))) (S.gotos [] [])
        S.qEnd) n))) n)) (S.gotos [] [])
      (S.qStat (S.sIf (S.eIndex I (S.eCell c_a) (S.eStr "all".toList)) (S.block (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mMethod I (S.eParen (S.eStr "(%d tasks)".toList)) "format" (S.lLast (S.mOne (S.eUn .len (S.eCell c_rows)))))))) (S.gotos [] [])
        S.qEnd)) (S.block (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mMethod I (S.eParen (S.eStr "(%d shown, %d done)".toList)) "format" (S.lCons (S.eUn .len (S.eCell c_rows)) (S.lLast (S.mOne (S.eIndex I (S.eFirst (S.mMethod I (S.eCell c_c) "one" (S.lLast (S.mOne (S.eStr "select count(*) n from task where state='done'".toList))))) (S.eStr "n".toList))))))))) (S.gotos [] [])
        S.qEnd))) (S.gotos [] [])
      (S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mMethod I (S.eCell c_c) "all" (S.lLast (S.mOne (S.eStr "select name, role, stay from agent where ended is null and stay is not null order by name".toList))))))) fun n => S.let1 fun c__2 => S.let1 fun c_x1 => S.letEnd ((S.block (S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mMethod I (S.eParen (S.eStr "staying: %s%s: %s".toList)) "format" (S.lCons (S.eIndex I (S.eCell c_x1) (S.eStr "name".toList)) (S.lCons (S.eOr (S.eAnd (S.eIndex I (S.eCell c_x1) (S.eStr "role".toList)) (S.eParen (S.eBin I .concat (S.eStr " ".toList) (S.eIndex I (S.eCell c_x1) (S.eStr "role".toList))))) (S.eStr "".toList)) (S.lLast (S.mOne (S.eIndex I (S.eCell c_x1) (S.eStr "stay".toList)))))))))) (S.gotos [] [])
        S.qEnd)) n)) (S.gotos [] [])
      S.qEnd)))) n))) n))) n))) n)) n))) n)

theorem M_cmd_board_ok (I : Sem) (env0 : Env) (c_M c_agents c_py c_d c_util c_ids : Nat)
    (h_M : env0.lookup "M" = some c_M)
    (h_agents : env0.lookup "agents" = some c_agents)
    (h_py : env0.lookup "py" = some c_py)
    (h_d : env0.lookup "d" = some c_d)
    (h_util : env0.lookup "util" = some c_util)
    (h_ids : env0.lookup "ids" = some c_ids)
    (h_require : env0.lookup "require" = none)
    (h_print : env0.lookup "print" = none)
    (h_ipairs : env0.lookup "ipairs" = none)
    (h_math : env0.lookup "math" = none) :
    CFn I (M_cmd_board I env0 c_M c_agents c_py c_d c_util c_ids) ⟨["c", "a"], false, M_cmd_board_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_c => CBs_let fun c_a => CBs_end ((CK_block (CQ_local (CL_last (CM_call (CE_glob h_require) (CL_last (CM_one rfl CE_str)))) fun n => CBs_let fun c_machine => CBs_end
      ((CQ_local (CL_last (CM_call (CE_index (CE_cell rfl) CE_str) CL_nil)) fun n => CBs_let fun c_avail => CBs_let fun c_total => CBs_let fun c_psi => CBs_end
      ((CQ_stat (CS_if (CE_cell rfl) (CK_block (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_call (CE_index (CE_cell rfl) CE_str) (CL_cons (CE_cell rfl) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl)))))))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_local (CL_last (CM_one rfl (CE_table CF_nil))) fun n => CBs_let fun c_role => CBs_end
      ((CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_method (CE_cell rfl) (CL_last (CM_one rfl CE_str)))))) fun n => CBs_let fun c__ => CBs_let fun c_x => CBs_end ((CK_block (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_index (CE_cell rfl) CE_str) CP_nil) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))
        CQ_end rfl rfl rfl)) n))
      (CQ_local (CL_last (CM_method (CE_cell rfl) (CL_last (CM_one rfl (CE_bin CE_str (CE_bin (CE_paren (CE_or (CE_and (CE_index (CE_cell rfl) CE_str) CE_str) CE_str)) (CE_bin CE_str (CE_bin (CE_index (CE_cell h_M) CE_str) CE_str)))))))) fun n => CBs_let fun c_rows => CBs_end
      ((CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_call (CE_index (CE_cell h_agents) CE_str) (CL_last (CM_one rfl (CE_cell rfl)))))))
      (CQ_local (CL_last (CM_method (CE_cell rfl) (CL_last (CM_one rfl CE_str)))) fun n => CBs_let fun c_held => CBs_end
      ((CQ_stat (CS_if (CE_cell rfl) (CK_block (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_one rfl (CE_cell rfl))))) fun n => CBs_let fun c__1 => CBs_let fun c_r => CBs_end ((CK_block (CQ_local (CL_last (CM_one rfl (CE_bin (CE_paren (CE_or (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) CE_str)) (CE_paren (CE_or (CE_and (CE_index (CE_cell rfl) (CE_index (CE_cell rfl) CE_str)) (CE_paren (CE_bin CE_str (CE_bin (CE_index (CE_cell rfl) (CE_index (CE_cell rfl) CE_str)) CE_str)))) CE_str))))) fun n => CBs_let fun c_who => CBs_end
        ((CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_cons (CE_cell rfl) (CL_cons (CE_or (CE_index (CE_cell rfl) CE_str) CE_str) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))))))))
          CQ_end rfl rfl rfl)) (CK_block (CQ_local (CL_last (CM_one rfl CE_str)) fun n => CBs_let fun c_lease => CBs_end
          ((CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_local (CL_last (CM_one rfl (CE_bin (CE_paren (CE_or (CE_index (CE_cell rfl) CE_str) CE_num)) (CE_call (CM_call (CE_index (CE_cell h_util) CE_str) CL_nil))))) fun n => CBs_let fun c_left => CBs_end
            ((CQ_stat (CS_assign (CP_var (wCell_ok rfl) CP_nil) (CL_last (CM_one rfl (CE_or (CE_and (CE_bin (CE_cell rfl) CE_num) (CE_method (CM_method (CE_paren CE_str) (CL_last (CM_call (CE_index (CE_glob h_math) CE_str) (CL_last (CM_one rfl (CE_bin (CE_cell rfl) CE_num)))))))) CE_str))))
            CQ_end rfl rfl rfl) n))) (CK_block CQ_end))
          (CQ_local (CL_last (CM_call (CE_index (CE_cell h_M) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl)))))) fun n => CBs_let fun c_u => CBs_end
          ((CQ_local (CL_last (CM_one rfl (CE_or (CE_and (CE_bin (CE_un (CE_cell rfl)) CE_num) (CE_paren (CE_bin CE_str (CE_call (CM_call (CE_cell h_ids) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_func (by rfl)))))))))) CE_str))) fun n => CBs_let fun c_wait => CBs_end
          ((CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_one rfl (CE_bin (CE_method (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_cons (CE_cell rfl) (CL_cons (CE_cell rfl) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))))) (CE_bin (CE_paren (CE_or (CE_and (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) CE_str) CE_str)) (CE_paren (CE_or (CE_and (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CE_paren (CE_bin CE_str (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str)))) CE_str))))))))
          CQ_end rfl rfl rfl) n)) n)) rfl rfl rfl) n))))
        CQ_end rfl rfl rfl) n))) n))
      (CQ_stat (CS_if (CE_index (CE_cell rfl) CE_str) (CK_block (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_method (CE_paren CE_str) (CL_last (CM_one rfl (CE_un (CE_cell rfl))))))))
        CQ_end rfl rfl rfl)) (CK_block (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_un (CE_cell rfl)) (CL_last (CM_one rfl (CE_index (CE_method (CM_method (CE_cell rfl) (CL_last (CM_one rfl CE_str)))) CE_str))))))))
        CQ_end rfl rfl rfl)))
      (CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_method (CE_cell rfl) (CL_last (CM_one rfl CE_str)))))) fun n => CBs_let fun c__2 => CBs_let fun c_x1 => CBs_end ((CK_block (CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_cons (CE_or (CE_and (CE_index (CE_cell rfl) CE_str) (CE_paren (CE_bin CE_str (CE_index (CE_cell rfl) CE_str)))) CE_str) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))))
        CQ_end rfl rfl rfl)) n))
      CQ_end rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) n)) rfl rfl rfl) n)) rfl rfl rfl) n)) rfl rfl rfl) n)) n))) n)

def M_cmd_rules (I : Sem) (env0 : Env) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_c => S.let1 fun c_a => S.letEnd ((S.block (S.qStat (S.sIf (S.eBin I .eq (S.eIndex I (S.eCell c_a) (S.eStr "act".toList)) (S.eStr "set".toList)) (S.block (S.qStat (S.sCall (S.mMethod I (S.eCell c_c) "exec" (S.lCons (S.eStr "insert or replace into meta(k,v) values('rules',?)".toList) (S.lLast (S.mCall I (S.eIndex I (S.eGlob "table") (S.eStr "concat".toList)) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "text".toList)) (S.lLast (S.mOne (S.eStr " ".toList))))))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qLocal (S.lLast (S.mMethod I (S.eCell c_c) "one" (S.lLast (S.mOne (S.eStr "select v from meta where k='rules'".toList))))) fun n => S.let1 fun c_r => S.letEnd
      ((S.qStat (S.sCall (S.mCall I (S.eGlob "print") (S.lLast (S.mOne (S.eOr (S.eAnd (S.eCell c_r) (S.eParen (S.eOr (S.eIndex I (S.eCell c_r) (S.eStr "v".toList)) (S.eStr "None".toList)))) (S.eStr "(none)".toList)))))) (S.gotos [] [])
      S.qEnd) n)))) n)

theorem M_cmd_rules_ok (I : Sem) (env0 : Env)
    (h_table : env0.lookup "table" = none)
    (h_print : env0.lookup "print" = none) :
    CFn I (M_cmd_rules I env0) ⟨["c", "a"], false, M_cmd_rules_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_c => CBs_let fun c_a => CBs_end ((CK_block (CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_stat (CS_call (CM_method (CE_cell rfl) (CL_cons CE_str (CL_last (CM_call (CE_index (CE_glob h_table) CE_str) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_last (CM_one rfl CE_str))))))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_local (CL_last (CM_method (CE_cell rfl) (CL_last (CM_one rfl CE_str)))) fun n => CBs_let fun c_r => CBs_end
      ((CQ_stat (CS_call (CM_call (CE_glob h_print) (CL_last (CM_one rfl (CE_or (CE_and (CE_cell rfl) (CE_paren (CE_or (CE_index (CE_cell rfl) CE_str) CE_str))) CE_str)))))
      CQ_end rfl rfl rfl) n)) rfl rfl rfl)) n)

def M_reserve (I : Sem) (env0 : Env) (c_util c_agents c_d c_M c_ids c_owned c_db : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_c => S.let1 fun c_name => S.let1 fun c_tid => S.let1 fun c_model => S.letEnd ((S.block (S.qLocal (S.lLast (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "now".toList)) S.lNil)) fun n => S.let1 fun c_t => S.letEnd
      ((S.qStat (S.sReturn (S.lLast (S.mMethod I (S.eCell c_c) "tx" (S.lLast (S.mOne (S.eFunc [] false M_reserve_fn_body (("t", c_t) :: ("model", c_model) :: ("tid", c_tid) :: ("name", c_name) :: ("c", c_c) :: env0))))))) (S.gotos [] [])
      S.qEnd) n))) n)

theorem M_reserve_ok (I : Sem) (env0 : Env) (c_util c_agents c_d c_M c_ids c_owned c_db : Nat)
    (h_util : env0.lookup "util" = some c_util)
    (h_agents : env0.lookup "agents" = some c_agents)
    (h_d : env0.lookup "d" = some c_d)
    (h_M : env0.lookup "M" = some c_M)
    (h_ids : env0.lookup "ids" = some c_ids)
    (h_owned : env0.lookup "owned" = some c_owned)
    (h_db : env0.lookup "db" = some c_db)
    (h_error : env0.lookup "error" = none) :
    CFn I (M_reserve I env0 c_util c_agents c_d c_M c_ids c_owned c_db) ⟨["c", "name", "tid", "model"], false, M_reserve_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_c => CBs_let fun c_name => CBs_let fun c_tid => CBs_let fun c_model => CBs_end ((CK_block (CQ_local (CL_last (CM_call (CE_index (CE_cell h_util) CE_str) CL_nil)) fun n => CBs_let fun c_t => CBs_end
      ((CQ_stat (CS_return (CL_last (CM_method (CE_cell rfl) (CL_last (CM_one rfl (CE_func (by rfl)))))))
      CQ_end rfl rfl rfl) n))) n)

def M_unreserve (I : Sem) (env0 : Env) (c_util : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_c => S.let1 fun c_name => S.let1 fun c_r => S.letEnd ((S.block (S.qStat (S.sCall (S.mMethod I (S.eCell c_c) "tx" (S.lLast (S.mOne (S.eFunc [] false M_unreserve_fn_body (("r", c_r) :: ("name", c_name) :: ("c", c_c) :: env0)))))) (S.gotos [] [])
      S.qEnd)) n)

theorem M_unreserve_ok (I : Sem) (env0 : Env) (c_util : Nat)
    (h_util : env0.lookup "util" = some c_util) :
    CFn I (M_unreserve I env0 c_util) ⟨["c", "name", "r"], false, M_unreserve_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_c => CBs_let fun c_name => CBs_let fun c_r => CBs_end ((CK_block (CQ_stat (CS_call (CM_method (CE_cell rfl) (CL_last (CM_one rfl (CE_func (by rfl))))))
      CQ_end rfl rfl rfl)) n)

def ts (I : Sem) (env0 : Env) (c_evs : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_k => S.let1 fun c_agg => S.letEnd ((S.block (S.qLocal S.lNil fun n => S.let1 fun c_v => S.letEnd
      ((S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mOne (S.eCell c_evs))))) fun n => S.let1 fun c__ => S.let1 fun c_e => S.letEnd ((S.block (S.qLocal (S.lLast (S.mOne (S.eOr (S.eAnd (S.eBin I .eq (S.eIndex I (S.eCell c_e) (S.eStr "kind".toList)) (S.eStr "spawn".toList)) (S.eStr "claim".toList)) (S.eIndex I (S.eCell c_e) (S.eStr "kind".toList))))) fun n => S.let1 fun c_kind => S.letEnd
        ((S.qStat (S.sIf (S.eBin I .eq (S.eCell c_kind) (S.eCell c_k)) (S.block (S.qStat (S.sAssign (S.pVar (S.wCell c_v) S.pNil) (S.lLast (S.mOne (S.eOr (S.eAnd (S.eCell c_v) (S.eFirst (S.mCall I (S.eCell c_agg) (S.lCons (S.eCell c_v) (S.lLast (S.mOne (S.eIndex I (S.eCell c_e) (S.eStr "ts".toList)))))))) (S.eIndex I (S.eCell c_e) (S.eStr "ts".toList)))))) (S.gotos [] [])
          S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
        S.qEnd) n))) n)) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lLast (S.mOne (S.eCell c_v)))) (S.gotos [] [])
      S.qEnd)) n))) n)

theorem ts_ok (I : Sem) (env0 : Env) (c_evs : Nat)
    (h_evs : env0.lookup "evs" = some c_evs)
    (h_ipairs : env0.lookup "ipairs" = none) :
    CFn I (ts I env0 c_evs) ⟨["k", "agg"], false, ts_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_k => CBs_let fun c_agg => CBs_end ((CK_block (CQ_local CL_nil fun n => CBs_let fun c_v => CBs_end
      ((CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_one rfl (CE_cell h_evs))))) fun n => CBs_let fun c__ => CBs_let fun c_e => CBs_end ((CK_block (CQ_local (CL_last (CM_one rfl (CE_or (CE_and (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) CE_str) (CE_index (CE_cell rfl) CE_str)))) fun n => CBs_let fun c_kind => CBs_end
        ((CQ_stat (CS_if (CE_bin (CE_cell rfl) (CE_cell rfl)) (CK_block (CQ_stat (CS_assign (CP_var (wCell_ok rfl) CP_nil) (CL_last (CM_one rfl (CE_or (CE_and (CE_cell rfl) (CE_call (CM_call (CE_cell rfl) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))))) (CE_index (CE_cell rfl) CE_str)))))
          CQ_end rfl rfl rfl)) (CK_block CQ_end))
        CQ_end rfl rfl rfl) n))) n))
      (CQ_stat (CS_return (CL_last (CM_one rfl (CE_cell rfl))))
      CQ_end rfl rfl rfl) rfl rfl rfl) n))) n)

def span (I : Sem) (env0 : Env) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_a => S.let1 fun c_b => S.letEnd ((S.block (S.qStat (S.sReturn (S.lLast (S.mOne (S.eOr (S.eAnd (S.eAnd (S.eBin I .ne (S.eCell c_a) S.eNil) (S.eBin I .ne (S.eCell c_b) S.eNil)) (S.eBin I .sub (S.eCell c_b) (S.eCell c_a))) S.eNil)))) (S.gotos [] [])
      S.qEnd)) n)

theorem span_ok (I : Sem) (env0 : Env) :
    CFn I (span I env0) ⟨["a", "b"], false, span_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_a => CBs_let fun c_b => CBs_end ((CK_block (CQ_stat (CS_return (CL_last (CM_one rfl (CE_or (CE_and (CE_and (CE_bin (CE_cell rfl) CE_nil) (CE_bin (CE_cell rfl) CE_nil)) (CE_bin (CE_cell rfl) (CE_cell rfl))) CE_nil))))
      CQ_end rfl rfl rfl)) n)

def M_cmd_task_fn (I : Sem) (env0 : Env) (c_no_task_to_wait_on c_c c_deps c_d c_a c_n c_py c_t c_db : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.letEnd ((S.block (S.qStat (S.sCall (S.mCall I (S.eCell c_no_task_to_wait_on) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eCell c_deps)))))) (S.gotos [] [])
      (S.qLocal (S.lLast (S.mOne (S.eTable S.fNil))) fun n => S.let1 fun c_ds => S.letEnd
      ((S.qStat (S.sForIn I (S.lLast (S.mCall I (S.eGlob "ipairs") (S.lLast (S.mOne (S.eCell c_deps))))) fun n => S.let1 fun c_i => S.let1 fun c_x => S.letEnd ((S.block (S.qStat (S.sAssign (S.pIndex I (S.eCell c_ds) (S.eCell c_i) S.pNil) (S.lLast (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eCell c_x)))))) (S.gotos [] [])
        S.qEnd)) n)) (S.gotos [] [])
      (S.qStat (S.sCall (S.mMethod I (S.eCell c_c) "exec" (S.lCons (S.eStr "insert into task(title,body,created_by,deps,model,effort,base,created_at) values(?,?,?,?,?,?,?,?)".toList) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "title".toList)) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "body".toList)) (S.lCons (S.eCell c_n) (S.lCons (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mCall I (S.eIndex I (S.eGlob "table") (S.eStr "concat".toList)) (S.lCons (S.eCell c_ds) (S.lLast (S.mOne (S.eStr ",".toList)))))))) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "model".toList)) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "effort".toList)) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "base".toList)) (S.lLast (S.mOne (S.eCell c_t))))))))))))) (S.gotos [] [])
      (S.qLocal (S.lLast (S.mMethod I (S.eCell c_c) "last_id" S.lNil)) fun n => S.let1 fun c_id => S.letEnd
      ((S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_db) (S.eStr "log".toList)) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_n) (S.lCons (S.eStr "task-add".toList) (S.lCons S.eNil (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s %s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eCell c_id))))) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "title".toList))))))))))))) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lLast (S.mOne (S.eCell c_id)))) (S.gotos [] [])
      S.qEnd)) n)))) n)))) n)

theorem M_cmd_task_fn_ok (I : Sem) (env0 : Env) (c_no_task_to_wait_on c_c c_deps c_d c_a c_n c_py c_t c_db : Nat)
    (h_no_task_to_wait_on : env0.lookup "no_task_to_wait_on" = some c_no_task_to_wait_on)
    (h_c : env0.lookup "c" = some c_c)
    (h_deps : env0.lookup "deps" = some c_deps)
    (h_d : env0.lookup "d" = some c_d)
    (h_a : env0.lookup "a" = some c_a)
    (h_n : env0.lookup "n" = some c_n)
    (h_py : env0.lookup "py" = some c_py)
    (h_t : env0.lookup "t" = some c_t)
    (h_db : env0.lookup "db" = some c_db)
    (h_ipairs : env0.lookup "ipairs" = none)
    (h_table : env0.lookup "table" = none) :
    CFn I (M_cmd_task_fn I env0 c_no_task_to_wait_on c_c c_deps c_d c_a c_n c_py c_t c_db) ⟨[], false, M_cmd_task_fn_body, env0⟩ :=
  CFn_fn fun args n => CBs_end ((CK_block (CQ_stat (CS_call (CM_call (CE_cell h_no_task_to_wait_on) (CL_cons (CE_cell h_c) (CL_last (CM_one rfl (CE_cell h_deps))))))
      (CQ_local (CL_last (CM_one rfl (CE_table CF_nil))) fun n => CBs_let fun c_ds => CBs_end
      ((CQ_stat (CS_forin (CL_last (CM_call (CE_glob h_ipairs) (CL_last (CM_one rfl (CE_cell h_deps))))) fun n => CBs_let fun c_i => CBs_let fun c_x => CBs_end ((CK_block (CQ_stat (CS_assign (CP_index (CE_cell rfl) (CE_cell rfl) CP_nil) (CL_last (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_cell rfl))))))
        CQ_end rfl rfl rfl)) n))
      (CQ_stat (CS_call (CM_method (CE_cell h_c) (CL_cons CE_str (CL_cons (CE_index (CE_cell h_a) CE_str) (CL_cons (CE_index (CE_cell h_a) CE_str) (CL_cons (CE_cell h_n) (CL_cons (CE_call (CM_call (CE_cell h_py) (CL_last (CM_call (CE_index (CE_glob h_table) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl CE_str))))))) (CL_cons (CE_index (CE_cell h_a) CE_str) (CL_cons (CE_index (CE_cell h_a) CE_str) (CL_cons (CE_index (CE_cell h_a) CE_str) (CL_last (CM_one rfl (CE_cell h_t)))))))))))))
      (CQ_local (CL_last (CM_method (CE_cell h_c) CL_nil)) fun n => CBs_let fun c_id => CBs_end
      ((CQ_stat (CS_call (CM_call (CE_index (CE_cell h_db) CE_str) (CL_cons (CE_cell h_c) (CL_cons (CE_cell h_n) (CL_cons CE_str (CL_cons CE_nil (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_cell rfl))))) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))))))))))
      (CQ_stat (CS_return (CL_last (CM_one rfl (CE_cell rfl))))
      CQ_end rfl rfl rfl) rfl rfl rfl) n)) rfl rfl rfl) rfl rfl rfl) n)) rfl rfl rfl)) n)

def f (I : Sem) (env0 : Env) (c_tm : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_k => S.letEnd ((S.block (S.qStat (S.sReturn (S.lLast (S.mOne (S.eOr (S.eAnd (S.eBin I .ne (S.eIndex I (S.eCell c_tm) (S.eCell c_k)) S.eNil) (S.eFirst (S.mMethod I (S.eParen (S.eStr "%dm".toList)) "format" (S.lLast (S.mCall I (S.eIndex I (S.eGlob "math") (S.eStr "floor".toList)) (S.lLast (S.mOne (S.eBin I .div (S.eIndex I (S.eCell c_tm) (S.eCell c_k)) (S.eNum (.int 60)))))))))) (S.eStr "-".toList))))) (S.gotos [] [])
      S.qEnd)) n)

theorem f_ok (I : Sem) (env0 : Env) (c_tm : Nat)
    (h_tm : env0.lookup "tm" = some c_tm)
    (h_math : env0.lookup "math" = none) :
    CFn I (f I env0 c_tm) ⟨["k"], false, f_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_k => CBs_end ((CK_block (CQ_stat (CS_return (CL_last (CM_one rfl (CE_or (CE_and (CE_bin (CE_index (CE_cell h_tm) (CE_cell rfl)) CE_nil) (CE_method (CM_method (CE_paren CE_str) (CL_last (CM_call (CE_index (CE_glob h_math) CE_str) (CL_last (CM_one rfl (CE_bin (CE_index (CE_cell h_tm) (CE_cell rfl)) CE_num)))))))) CE_str))))
      CQ_end rfl rfl rfl)) n)

def M_cmd_task_fn1 (I : Sem) (env0 : Env) (c_c c_a c_util c_d c_M c_db c_n c_py : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.letEnd ((S.block (S.qLocal (S.lLast (S.mMethod I (S.eCell c_c) "one" (S.lCons (S.eStr "select * from task where id=?".toList) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList))))))) fun n => S.let1 fun c_r2 => S.letEnd
      ((S.qStat (S.sIf (S.eBin I .ne (S.eIndex I (S.eCell c_r2) (S.eStr "state".toList)) (S.eStr "open".toList)) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "task #%s is %s; only an open task's dependencies can change".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r2) (S.eStr "state".toList))))))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qLocal (S.lLast (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "set_deps".toList)) (S.lCons (S.eCell c_c) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "deps".toList)))))))) fun n => S.let1 fun c_ds => S.letEnd
      ((S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_db) (S.eStr "log".toList)) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_n) (S.lCons (S.eStr "task-after".toList) (S.lCons S.eNil (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s after %s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lLast (S.mOne (S.eOr (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mCall I (S.eIndex I (S.eGlob "table") (S.eStr "concat".toList)) (S.lCons (S.eCell c_ds) (S.lLast (S.mOne (S.eStr ",".toList)))))))) (S.eStr "-".toList))))))))))))) (S.gotos [] [])
      S.qEnd) n))) n))) n)

theorem M_cmd_task_fn1_ok (I : Sem) (env0 : Env) (c_c c_a c_util c_d c_M c_db c_n c_py : Nat)
    (h_c : env0.lookup "c" = some c_c)
    (h_a : env0.lookup "a" = some c_a)
    (h_util : env0.lookup "util" = some c_util)
    (h_d : env0.lookup "d" = some c_d)
    (h_M : env0.lookup "M" = some c_M)
    (h_db : env0.lookup "db" = some c_db)
    (h_n : env0.lookup "n" = some c_n)
    (h_py : env0.lookup "py" = some c_py)
    (h_table : env0.lookup "table" = none) :
    CFn I (M_cmd_task_fn1 I env0 c_c c_a c_util c_d c_M c_db c_n c_py) ⟨[], false, M_cmd_task_fn1_body, env0⟩ :=
  CFn_fn fun args n => CBs_end ((CK_block (CQ_local (CL_last (CM_method (CE_cell h_c) (CL_cons CE_str (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str)))))) fun n => CBs_let fun c_r2 => CBs_end
      ((CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_local (CL_last (CM_call (CE_index (CE_cell h_M) CE_str) (CL_cons (CE_cell h_c) (CL_cons (CE_index (CE_cell h_a) CE_str) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))))) fun n => CBs_let fun c_ds => CBs_end
      ((CQ_stat (CS_call (CM_call (CE_index (CE_cell h_db) CE_str) (CL_cons (CE_cell h_c) (CL_cons (CE_cell h_n) (CL_cons CE_str (CL_cons CE_nil (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))) (CL_last (CM_one rfl (CE_or (CE_call (CM_call (CE_cell h_py) (CL_last (CM_call (CE_index (CE_glob h_table) CE_str) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl CE_str))))))) CE_str))))))))))))
      CQ_end rfl rfl rfl) n)) rfl rfl rfl) n))) n)

def M_cmd_task_fn2 (I : Sem) (env0 : Env) (c_c c_mine c_a c_t c_n c_util c_d c_db : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.letEnd ((S.block (S.qStat (S.sIf (S.eBin I .eq (S.eFirst (S.mMethod I (S.eCell c_c) "exec" (S.lCons (S.eBin I .concat (S.eStr "update task set state='done', evidence=?, lease_until=null, done_at=?, ".toList) (S.eBin I .concat (S.eStr "done_ctx=(select ctx_tokens from agent where name=?)".toList) (S.eCell c_mine))) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "evidence".toList)) (S.lCons (S.eCell c_t) (S.lCons (S.eCell c_n) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)) (S.lLast (S.mOne (S.eCell c_n)))))))))) (S.eNum (.int 0))) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "task #%s is not claimed by you".toList)) "format" (S.lLast (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_db) (S.eStr "log".toList)) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_n) (S.lCons (S.eStr "done".toList) (S.lCons S.eNil (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s %s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "evidence".toList))))))))))))) (S.gotos [] [])
      S.qEnd))) n)

theorem M_cmd_task_fn2_ok (I : Sem) (env0 : Env) (c_c c_mine c_a c_t c_n c_util c_d c_db : Nat)
    (h_c : env0.lookup "c" = some c_c)
    (h_mine : env0.lookup "mine" = some c_mine)
    (h_a : env0.lookup "a" = some c_a)
    (h_t : env0.lookup "t" = some c_t)
    (h_n : env0.lookup "n" = some c_n)
    (h_util : env0.lookup "util" = some c_util)
    (h_d : env0.lookup "d" = some c_d)
    (h_db : env0.lookup "db" = some c_db) :
    CFn I (M_cmd_task_fn2 I env0 c_c c_mine c_a c_t c_n c_util c_d c_db) ⟨[], false, M_cmd_task_fn2_body, env0⟩ :=
  CFn_fn fun args n => CBs_end ((CK_block (CQ_stat (CS_if (CE_bin (CE_method (CM_method (CE_cell h_c) (CL_cons (CE_bin CE_str (CE_bin CE_str (CE_cell h_mine))) (CL_cons (CE_index (CE_cell h_a) CE_str) (CL_cons (CE_cell h_t) (CL_cons (CE_cell h_n) (CL_cons (CE_index (CE_cell h_a) CE_str) (CL_last (CM_one rfl (CE_cell h_n)))))))))) CE_num) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_last (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str)))))))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_db) CE_str) (CL_cons (CE_cell h_c) (CL_cons (CE_cell h_n) (CL_cons CE_str (CL_cons CE_nil (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))))))))))
      CQ_end rfl rfl rfl) rfl rfl rfl)) n)

def M_cmd_task_fn3 (I : Sem) (env0 : Env) (c_c c_a c_n c_util c_d c_db : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.letEnd ((S.block (S.qStat (S.sIf (S.eBin I .eq (S.eFirst (S.mMethod I (S.eCell c_c) "exec" (S.lCons (S.eStr "update task set state='blocked', question=? where id=? and owner=? and state='claimed'".toList) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "question".toList)) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)) (S.lLast (S.mOne (S.eCell c_n)))))))) (S.eNum (.int 0))) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "task #%s is not claimed by you".toList)) "format" (S.lLast (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_db) (S.eStr "log".toList)) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_n) (S.lCons (S.eStr "block".toList) (S.lCons S.eNil (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s %s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "question".toList))))))))))))) (S.gotos [] [])
      S.qEnd))) n)

theorem M_cmd_task_fn3_ok (I : Sem) (env0 : Env) (c_c c_a c_n c_util c_d c_db : Nat)
    (h_c : env0.lookup "c" = some c_c)
    (h_a : env0.lookup "a" = some c_a)
    (h_n : env0.lookup "n" = some c_n)
    (h_util : env0.lookup "util" = some c_util)
    (h_d : env0.lookup "d" = some c_d)
    (h_db : env0.lookup "db" = some c_db) :
    CFn I (M_cmd_task_fn3 I env0 c_c c_a c_n c_util c_d c_db) ⟨[], false, M_cmd_task_fn3_body, env0⟩ :=
  CFn_fn fun args n => CBs_end ((CK_block (CQ_stat (CS_if (CE_bin (CE_method (CM_method (CE_cell h_c) (CL_cons CE_str (CL_cons (CE_index (CE_cell h_a) CE_str) (CL_cons (CE_index (CE_cell h_a) CE_str) (CL_last (CM_one rfl (CE_cell h_n)))))))) CE_num) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_last (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str)))))))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_db) CE_str) (CL_cons (CE_cell h_c) (CL_cons (CE_cell h_n) (CL_cons CE_str (CL_cons CE_nil (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))))))))))
      CQ_end rfl rfl rfl) rfl rfl rfl)) n)

def M_cmd_task_fn4 (I : Sem) (env0 : Env) (c_c c_py c_a c_t c_M c_r c_util c_d c_db c_n : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.letEnd ((S.block (S.qStat (S.sIf (S.eBin I .eq (S.eFirst (S.mMethod I (S.eCell c_c) "exec" (S.lCons (S.eStr "update task set state='claimed', question=null, answer=coalesce(?, answer), lease_until=? where id=? and owner=? and state='blocked'".toList) (S.lCons (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "answer".toList)))))) (S.lCons (S.eBin I .add (S.eCell c_t) (S.eIndex I (S.eCell c_M) (S.eStr "LEASE".toList))) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "owner".toList)))))))))) (S.eNum (.int 0))) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "task #%s changed under you; `swarm task show %s`".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lLast (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList))))))))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_db) (S.eStr "log".toList)) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_n) (S.lCons (S.eStr "unblock".toList) (S.lCons S.eNil (S.lLast (S.mOne (S.eBin I .concat (S.eStr "#".toList) (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList))))))))))))))) (S.gotos [] [])
      (S.qStat (S.sIf (S.eAnd (S.eFirst (S.mCall I (S.eCell c_py) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "answer".toList)))))) (S.eBin I .ne (S.eCell c_n) (S.eIndex I (S.eCell c_r) (S.eStr "owner".toList)))) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eFirst (S.mCall I (S.eGlob "require") (S.lLast (S.mOne (S.eStr "swarm.msgs".toList))))) (S.eStr "post".toList)) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_n) (S.lCons (S.eIndex I (S.eCell c_r) (S.eStr "owner".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s is unblocked. Answer: %s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "answer".toList)))))))))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      S.qEnd)))) n)

theorem M_cmd_task_fn4_ok (I : Sem) (env0 : Env) (c_c c_py c_a c_t c_M c_r c_util c_d c_db c_n : Nat)
    (h_c : env0.lookup "c" = some c_c)
    (h_py : env0.lookup "py" = some c_py)
    (h_a : env0.lookup "a" = some c_a)
    (h_t : env0.lookup "t" = some c_t)
    (h_M : env0.lookup "M" = some c_M)
    (h_r : env0.lookup "r" = some c_r)
    (h_util : env0.lookup "util" = some c_util)
    (h_d : env0.lookup "d" = some c_d)
    (h_db : env0.lookup "db" = some c_db)
    (h_n : env0.lookup "n" = some c_n)
    (h_require : env0.lookup "require" = none) :
    CFn I (M_cmd_task_fn4 I env0 c_c c_py c_a c_t c_M c_r c_util c_d c_db c_n) ⟨[], false, M_cmd_task_fn4_body, env0⟩ :=
  CFn_fn fun args n => CBs_end ((CK_block (CQ_stat (CS_if (CE_bin (CE_method (CM_method (CE_cell h_c) (CL_cons CE_str (CL_cons (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))) (CL_cons (CE_bin (CE_cell h_t) (CE_index (CE_cell h_M) CE_str)) (CL_cons (CE_index (CE_cell h_a) CE_str) (CL_last (CM_one rfl (CE_index (CE_cell h_r) CE_str))))))))) CE_num) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))) (CL_last (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))))))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_db) CE_str) (CL_cons (CE_cell h_c) (CL_cons (CE_cell h_n) (CL_cons CE_str (CL_cons CE_nil (CL_last (CM_one rfl (CE_bin CE_str (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))))))))))))
      (CQ_stat (CS_if (CE_and (CE_call (CM_call (CE_cell h_py) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))) (CE_bin (CE_cell h_n) (CE_index (CE_cell h_r) CE_str))) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_call (CM_call (CE_glob h_require) (CL_last (CM_one rfl CE_str)))) CE_str) (CL_cons (CE_cell h_c) (CL_cons (CE_cell h_n) (CL_cons (CE_index (CE_cell h_r) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str)))))))))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      CQ_end rfl rfl rfl) rfl rfl rfl) rfl rfl rfl)) n)

def M_cmd_task_fn5 (I : Sem) (env0 : Env) (c_c c_a c_n c_util c_d c_M c_db : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.letEnd ((S.block (S.qStat (S.sIf (S.eBin I .eq (S.eFirst (S.mMethod I (S.eCell c_c) "exec" (S.lCons (S.eStr "update task set state='open', owner=null, lease_until=null where id=? and owner=? and state='claimed'".toList) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)) (S.lLast (S.mOne (S.eCell c_n))))))) (S.eNum (.int 0))) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "task #%s is not claimed by you".toList)) "format" (S.lLast (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qStat (S.sIf (S.eIndex I (S.eCell c_a) (S.eStr "after".toList)) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "set_deps".toList)) (S.lCons (S.eCell c_c) (S.lCons (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "after".toList)))))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_db) (S.eStr "log".toList)) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_n) (S.lCons (S.eStr "release".toList) (S.lCons S.eNil (S.lLast (S.mOne (S.eBin I .concat (S.eStr "#".toList) (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList))))))))))))))) (S.gotos [] [])
      S.qEnd)))) n)

theorem M_cmd_task_fn5_ok (I : Sem) (env0 : Env) (c_c c_a c_n c_util c_d c_M c_db : Nat)
    (h_c : env0.lookup "c" = some c_c)
    (h_a : env0.lookup "a" = some c_a)
    (h_n : env0.lookup "n" = some c_n)
    (h_util : env0.lookup "util" = some c_util)
    (h_d : env0.lookup "d" = some c_d)
    (h_M : env0.lookup "M" = some c_M)
    (h_db : env0.lookup "db" = some c_db) :
    CFn I (M_cmd_task_fn5 I env0 c_c c_a c_n c_util c_d c_M c_db) ⟨[], false, M_cmd_task_fn5_body, env0⟩ :=
  CFn_fn fun args n => CBs_end ((CK_block (CQ_stat (CS_if (CE_bin (CE_method (CM_method (CE_cell h_c) (CL_cons CE_str (CL_cons (CE_index (CE_cell h_a) CE_str) (CL_last (CM_one rfl (CE_cell h_n))))))) CE_num) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_last (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str)))))))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_stat (CS_if (CE_index (CE_cell h_a) CE_str) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_M) CE_str) (CL_cons (CE_cell h_c) (CL_cons (CE_index (CE_cell h_a) CE_str) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str)))))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_db) CE_str) (CL_cons (CE_cell h_c) (CL_cons (CE_cell h_n) (CL_cons CE_str (CL_cons CE_nil (CL_last (CM_one rfl (CE_bin CE_str (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))))))))))))
      CQ_end rfl rfl rfl) rfl rfl rfl) rfl rfl rfl)) n)

def M_cmd_task_fn6 (I : Sem) (env0 : Env) (c_c c_a c_n c_agents c_util c_d c_t c_db : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.letEnd ((S.block (S.qLocal (S.lLast (S.mMethod I (S.eCell c_c) "one" (S.lCons (S.eStr "select * from task where id=?".toList) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList))))))) fun n => S.let1 fun c_r2 => S.letEnd
      ((S.qStat (S.sIf (S.eAnd (S.eAnd (S.eParen (S.eOr (S.eBin I .eq (S.eIndex I (S.eCell c_r2) (S.eStr "state".toList)) (S.eStr "claimed".toList)) (S.eBin I .eq (S.eIndex I (S.eCell c_r2) (S.eStr "state".toList)) (S.eStr "blocked".toList)))) (S.eBin I .ne (S.eIndex I (S.eCell c_r2) (S.eStr "owner".toList)) (S.eCell c_n))) (S.eUn .not (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_agents) (S.eStr "is_comms".toList)) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eCell c_n)))))))) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s is %s by %s; only it or the communicator can drop it".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))) (S.lCons (S.eIndex I (S.eCell c_r2) (S.eStr "state".toList)) (S.lLast (S.mCall I (S.eGlob "tostring") (S.lLast (S.mOne (S.eIndex I (S.eCell c_r2) (S.eStr "owner".toList)))))))))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qStat (S.sCall (S.mMethod I (S.eCell c_c) "exec" (S.lCons (S.eStr "update task set state='dropped', owner=null, lease_until=null, dropped_at=? where id=?".toList) (S.lCons (S.eCell c_t) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList)))))))) (S.gotos [] [])
      (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_db) (S.eStr "log".toList)) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_n) (S.lCons (S.eStr "drop".toList) (S.lCons S.eNil (S.lLast (S.mOne (S.eBin I .concat (S.eStr "#".toList) (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_a) (S.eStr "id".toList))))))))))))))) (S.gotos [] [])
      S.qEnd))) n))) n)

theorem M_cmd_task_fn6_ok (I : Sem) (env0 : Env) (c_c c_a c_n c_agents c_util c_d c_t c_db : Nat)
    (h_c : env0.lookup "c" = some c_c)
    (h_a : env0.lookup "a" = some c_a)
    (h_n : env0.lookup "n" = some c_n)
    (h_agents : env0.lookup "agents" = some c_agents)
    (h_util : env0.lookup "util" = some c_util)
    (h_d : env0.lookup "d" = some c_d)
    (h_t : env0.lookup "t" = some c_t)
    (h_db : env0.lookup "db" = some c_db)
    (h_tostring : env0.lookup "tostring" = none) :
    CFn I (M_cmd_task_fn6 I env0 c_c c_a c_n c_agents c_util c_d c_t c_db) ⟨[], false, M_cmd_task_fn6_body, env0⟩ :=
  CFn_fn fun args n => CBs_end ((CK_block (CQ_local (CL_last (CM_method (CE_cell h_c) (CL_cons CE_str (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str)))))) fun n => CBs_let fun c_r2 => CBs_end
      ((CQ_stat (CS_if (CE_and (CE_and (CE_paren (CE_or (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str))) (CE_bin (CE_index (CE_cell rfl) CE_str) (CE_cell h_n))) (CE_un (CE_call (CM_call (CE_index (CE_cell h_agents) CE_str) (CL_cons (CE_cell h_c) (CL_last (CM_one rfl (CE_cell h_n)))))))) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_last (CM_call (CE_glob h_tostring) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_stat (CS_call (CM_method (CE_cell h_c) (CL_cons CE_str (CL_cons (CE_cell h_t) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str)))))))
      (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_db) CE_str) (CL_cons (CE_cell h_c) (CL_cons (CE_cell h_n) (CL_cons CE_str (CL_cons CE_nil (CL_last (CM_one rfl (CE_bin CE_str (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell h_a) CE_str))))))))))))))
      CQ_end rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) n))) n)

def M_cmd_board_fn (I : Sem) (env0 : Env) (c_d : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_x => S.letEnd ((S.block (S.qStat (S.sReturn (S.lLast (S.mOne (S.eBin I .concat (S.eStr "#".toList) (S.eBin I .concat (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_x) (S.eStr "id".toList)))))) (S.eParen (S.eOr (S.eAnd (S.eBin I .eq (S.eIndex I (S.eCell c_x) (S.eStr "state".toList)) (S.eStr "dropped".toList)) (S.eStr " (dropped)".toList)) (S.eStr "".toList)))))))) (S.gotos [] [])
      S.qEnd)) n)

theorem M_cmd_board_fn_ok (I : Sem) (env0 : Env) (c_d : Nat)
    (h_d : env0.lookup "d" = some c_d) :
    CFn I (M_cmd_board_fn I env0 c_d) ⟨["x"], false, M_cmd_board_fn_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_x => CBs_end ((CK_block (CQ_stat (CS_return (CL_last (CM_one rfl (CE_bin CE_str (CE_bin (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))) (CE_paren (CE_or (CE_and (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) CE_str) CE_str)))))))
      CQ_end rfl rfl rfl)) n)

def M_reserve_fn (I : Sem) (env0 : Env) (c_agents c_c c_name c_model c_tid c_util c_d c_M c_ids c_owned c_t c_db : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.letEnd ((S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_agents) (S.eStr "reserve".toList)) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_name) (S.lLast (S.mOne (S.eCell c_model))))))) (S.gotos [] [])
      (S.qLocal (S.lLast (S.mMethod I (S.eCell c_c) "one" (S.lCons (S.eStr "select * from task where id=?".toList) (S.lLast (S.mOne (S.eCell c_tid)))))) fun n => S.let1 fun c_r => S.letEnd
      ((S.qStat (S.sIf (S.eUn .not (S.eCell c_r)) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mOne (S.eBin I .concat (S.eStr "no task #".toList) (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eCell c_tid)))))))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qLocal (S.lLast (S.mCall I (S.eIndex I (S.eCell c_M) (S.eStr "undone".toList)) (S.lCons (S.eCell c_c) (S.lLast (S.mOne (S.eCell c_r)))))) fun n => S.let1 fun c_u => S.letEnd
      ((S.qStat (S.sIf (S.eBin I .gt (S.eUn .len (S.eCell c_u)) (S.eNum (.int 0))) (S.block (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "die".toList)) (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s waits on %s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eCell c_tid))))) (S.lLast (S.mCall I (S.eCell c_ids) (S.lCons (S.eCell c_u) (S.lLast (S.mOne (S.eFunc ["x"] false M_reserve_fn_fn_body (("u", c_u) :: ("r", c_r) :: env0)))))))))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qStat (S.sIf (S.eBin I .ne (S.eIndex I (S.eCell c_r) (S.eStr "state".toList)) (S.eStr "open".toList)) (S.block (S.qStat (S.sCall (S.mCall I (S.eGlob "error") (S.lCons (S.eTable (S.fNamed "exit" (S.eNum (.int 1)) (S.fNamed "lost" (S.eFirst (S.mMethod I (S.eParen (S.eStr "task #%s is %s%s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eCell c_tid))))) (S.lCons (S.eIndex I (S.eCell c_r) (S.eStr "state".toList)) (S.lLast (S.mCall I (S.eCell c_owned) (S.lLast (S.mOne (S.eCell c_r))))))))) S.fNil))) (S.lLast (S.mOne (S.eNum (.int 0))))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qStat (S.sCall (S.mMethod I (S.eCell c_c) "exec" (S.lCons (S.eStr "update task set state='claimed', owner=?, lease_until=?, first_claimed_at=coalesce(first_claimed_at,?) where id=?".toList) (S.lCons (S.eCell c_name) (S.lCons (S.eBin I .add (S.eCell c_t) (S.eIndex I (S.eCell c_M) (S.eStr "LEASE".toList))) (S.lCons (S.eCell c_t) (S.lLast (S.mOne (S.eCell c_tid))))))))) (S.gotos [] [])
      (S.qStat (S.sCall (S.mCall I (S.eIndex I (S.eCell c_db) (S.eStr "log".toList)) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_name) (S.lCons (S.eStr "claim".toList) (S.lCons S.eNil (S.lLast (S.mMethod I (S.eParen (S.eStr "#%s %s".toList)) "format" (S.lCons (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eCell c_tid))))) (S.lLast (S.mOne (S.eIndex I (S.eCell c_r) (S.eStr "title".toList))))))))))))) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lLast (S.mOne (S.eCell c_r)))) (S.gotos [] [])
      S.qEnd))))) n))) n)))) n)

theorem M_reserve_fn_ok (I : Sem) (env0 : Env) (c_agents c_c c_name c_model c_tid c_util c_d c_M c_ids c_owned c_t c_db : Nat)
    (h_agents : env0.lookup "agents" = some c_agents)
    (h_c : env0.lookup "c" = some c_c)
    (h_name : env0.lookup "name" = some c_name)
    (h_model : env0.lookup "model" = some c_model)
    (h_tid : env0.lookup "tid" = some c_tid)
    (h_util : env0.lookup "util" = some c_util)
    (h_d : env0.lookup "d" = some c_d)
    (h_M : env0.lookup "M" = some c_M)
    (h_ids : env0.lookup "ids" = some c_ids)
    (h_owned : env0.lookup "owned" = some c_owned)
    (h_t : env0.lookup "t" = some c_t)
    (h_db : env0.lookup "db" = some c_db)
    (h_error : env0.lookup "error" = none) :
    CFn I (M_reserve_fn I env0 c_agents c_c c_name c_model c_tid c_util c_d c_M c_ids c_owned c_t c_db) ⟨[], false, M_reserve_fn_body, env0⟩ :=
  CFn_fn fun args n => CBs_end ((CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_agents) CE_str) (CL_cons (CE_cell h_c) (CL_cons (CE_cell h_name) (CL_last (CM_one rfl (CE_cell h_model)))))))
      (CQ_local (CL_last (CM_method (CE_cell h_c) (CL_cons CE_str (CL_last (CM_one rfl (CE_cell h_tid)))))) fun n => CBs_let fun c_r => CBs_end
      ((CQ_stat (CS_if (CE_un (CE_cell rfl)) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_one rfl (CE_bin CE_str (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_cell h_tid))))))))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_local (CL_last (CM_call (CE_index (CE_cell h_M) CE_str) (CL_cons (CE_cell h_c) (CL_last (CM_one rfl (CE_cell rfl)))))) fun n => CBs_let fun c_u => CBs_end
      ((CQ_stat (CS_if (CE_bin (CE_un (CE_cell rfl)) CE_num) (CK_block (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_util) CE_str) (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_cell h_tid))))) (CL_last (CM_call (CE_cell h_ids) (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_func (by rfl))))))))))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_stat (CS_if (CE_bin (CE_index (CE_cell rfl) CE_str) CE_str) (CK_block (CQ_stat (CS_call (CM_call (CE_glob h_error) (CL_cons (CE_table (CF_named CE_num (CF_named (CE_method (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_cell h_tid))))) (CL_cons (CE_index (CE_cell rfl) CE_str) (CL_last (CM_call (CE_cell h_owned) (CL_last (CM_one rfl (CE_cell rfl))))))))) CF_nil))) (CL_last (CM_one rfl CE_num)))))
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_stat (CS_call (CM_method (CE_cell h_c) (CL_cons CE_str (CL_cons (CE_cell h_name) (CL_cons (CE_bin (CE_cell h_t) (CE_index (CE_cell h_M) CE_str)) (CL_cons (CE_cell h_t) (CL_last (CM_one rfl (CE_cell h_tid)))))))))
      (CQ_stat (CS_call (CM_call (CE_index (CE_cell h_db) CE_str) (CL_cons (CE_cell h_c) (CL_cons (CE_cell h_name) (CL_cons CE_str (CL_cons CE_nil (CL_last (CM_method (CE_paren CE_str) (CL_cons (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_cell h_tid))))) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str))))))))))))
      (CQ_stat (CS_return (CL_last (CM_one rfl (CE_cell rfl))))
      CQ_end rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) rfl rfl rfl) n)) rfl rfl rfl) n)) rfl rfl rfl)) n)

def M_unreserve_fn (I : Sem) (env0 : Env) (c_c c_util c_name c_r : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.letEnd ((S.block (S.qStat (S.sCall (S.mMethod I (S.eCell c_c) "exec" (S.lCons (S.eStr "update agent set ended=? where name=? and hc is null".toList) (S.lCons (S.eFirst (S.mCall I (S.eIndex I (S.eCell c_util) (S.eStr "now".toList)) S.lNil)) (S.lLast (S.mOne (S.eCell c_name))))))) (S.gotos [] [])
      (S.qStat (S.sIf (S.eUn .not (S.eCell c_r)) (S.block (S.qStat (S.sReturn S.lNil) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qStat (S.sCall (S.mMethod I (S.eCell c_c) "exec" (S.lCons (S.eBin I .concat (S.eStr "update task set state='open', owner=null, lease_until=null, first_claimed_at=? where id=? and owner=? ".toList) (S.eStr "and state='claimed'".toList)) (S.lCons (S.eIndex I (S.eCell c_r) (S.eStr "first_claimed_at".toList)) (S.lCons (S.eIndex I (S.eCell c_r) (S.eStr "id".toList)) (S.lLast (S.mOne (S.eCell c_name)))))))) (S.gotos [] [])
      S.qEnd)))) n)

theorem M_unreserve_fn_ok (I : Sem) (env0 : Env) (c_c c_util c_name c_r : Nat)
    (h_c : env0.lookup "c" = some c_c)
    (h_util : env0.lookup "util" = some c_util)
    (h_name : env0.lookup "name" = some c_name)
    (h_r : env0.lookup "r" = some c_r) :
    CFn I (M_unreserve_fn I env0 c_c c_util c_name c_r) ⟨[], false, M_unreserve_fn_body, env0⟩ :=
  CFn_fn fun args n => CBs_end ((CK_block (CQ_stat (CS_call (CM_method (CE_cell h_c) (CL_cons CE_str (CL_cons (CE_call (CM_call (CE_index (CE_cell h_util) CE_str) CL_nil)) (CL_last (CM_one rfl (CE_cell h_name)))))))
      (CQ_stat (CS_if (CE_un (CE_cell h_r)) (CK_block (CQ_stat (CS_return CL_nil)
        CQ_end rfl rfl rfl)) (CK_block CQ_end))
      (CQ_stat (CS_call (CM_method (CE_cell h_c) (CL_cons (CE_bin CE_str CE_str) (CL_cons (CE_index (CE_cell h_r) CE_str) (CL_cons (CE_index (CE_cell h_r) CE_str) (CL_last (CM_one rfl (CE_cell h_name))))))))
      CQ_end rfl rfl rfl) rfl rfl rfl) rfl rfl rfl)) n)

def M_reserve_fn_fn (I : Sem) (env0 : Env) (c_d : Nat) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_x => S.letEnd ((S.block (S.qStat (S.sReturn (S.lLast (S.mOne (S.eBin I .concat (S.eStr "#".toList) (S.eFirst (S.mCall I (S.eCell c_d) (S.lLast (S.mOne (S.eIndex I (S.eCell c_x) (S.eStr "id".toList)))))))))) (S.gotos [] [])
      S.qEnd)) n)

theorem M_reserve_fn_fn_ok (I : Sem) (env0 : Env) (c_d : Nat)
    (h_d : env0.lookup "d" = some c_d) :
    CFn I (M_reserve_fn_fn I env0 c_d) ⟨["x"], false, M_reserve_fn_fn_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_x => CBs_end ((CK_block (CQ_stat (CS_return (CL_last (CM_one rfl (CE_bin CE_str (CE_call (CM_call (CE_cell h_d) (CL_last (CM_one rfl (CE_index (CE_cell rfl) CE_str)))))))))
      CQ_end rfl rfl rfl)) n)

end Swarm.Lifted.Tasks
-- checksum Swarm.Lifted.Tasks 4123707679
