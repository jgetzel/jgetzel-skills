import Tests.Cli.Fixture

/-! cli_stop_spec.lua: the Stop hook (board #90) blocks a stop until the agent is endable or has declared why it waits. -/

namespace SwarmLean.Tests.Cli.Stop
open SwarmLean.Tests.Cli
open Lean (Json toJson)

/-- The stop hook's reason, none when it let the stop through. -/
def stop (t : T) (who : String) (p : Json := Json.mkObj []) : IO (Option String) := do
  let p ← if p.f "cwd" == .null then pure (p.setObjVal! "cwd" (← t.cwdOf who)) else pure p
  let r ← t.sw who ["hook", "stop"] { stdin := p.compress }
  if strip r.stdout == "" then return none
  let o := (Json.parse r.stdout).toOption.getD .null
  eq (o.f "decision") "block"
  return (o.f "reason").s?

def claim (t : T) (who : String) : IO Unit := do
  discard <| t.sw who ["task", "add", "x"]; discard <| t.sw who ["task", "claim", "1"]

def test_endable_stops_through (t : T) : IO Unit := do
  t.agent "a"
  eq (← stop t "a") Json.null
  eq (← t.sw "a" ["endable", "--why"] { ok := true }).stdout ""

def test_claim_blocks_with_the_three_ways_out (t : T) : IO Unit := do
  t.agent "a"; claim t "a"
  let r ← stop t "a"
  has r "claim held (#1)"
  has r "swarm task release"; has r "swarm task block"; has r "swarm stay"
  let e ← t.sw "a" ["endable", "--why"] { ok := false }
  eq e.code 1; has e.stdout "claim held (#1)"

def test_lock_blocks (t : T) : IO Unit := do
  t.agent "a"; discard <| t.sw "a" ["lock", "a.txt"]
  has (← stop t "a") "lock held"

def test_blocked_task_and_stay_allow (t : T) : IO Unit := do
  t.agent "a"; claim t "a"
  discard <| t.sw "a" ["task", "block", "1", "which one?"]
  eq (← stop t "a") Json.null
  t.agent "b"; discard <| t.sw "b" ["stay", "reviews"]
  eq (← stop t "b") Json.null

def test_release_then_stop_is_endable (t : T) : IO Unit := do
  t.agent "a"; claim t "a"
  has (← stop t "a") "claim held"
  discard <| t.sw "a" ["task", "release", "1"]
  eq (← stop t "a") Json.null

def test_dirty_worktree_lists_files (t : T) : IO Unit := do
  t.agent "a" [("wt", t.wt)]
  t.setCwd "a" t.wt
  t.write "a" "new.txt" "x"
  let r ← stop t "a"
  has r "dirty worktree"; has r "new.txt"

def bg (cmd : String) : Json :=
  json% {"background_tasks": [{"status": "running", "command": $cmd}]}

def test_own_background_job_allows_but_swarm_wait_does_not (t : T) : IO Unit := do
  t.agent "a"; claim t "a"
  eq (← stop t "a" (bg "make test")) Json.null
  has (← stop t "a" (bg "swarm wait --timeout 60")) "claim held"

def test_error_turn_allows (t : T) : IO Unit := do
  t.agent "a"; claim t "a"
  let tr := t.d ++ "/e.jsonl"
  put tr ((json% {"type": "assistant", "isApiErrorMessage": true, "message": {"content": "rate limit"}}).compress ++ "\n")
  eq (← stop t "a" (json% {"transcript_path": $tr})) Json.null

def test_comms_is_exempt (t : T) : IO Unit := do
  t.agent "comms"; claim t "comms"
  discard <| t.q "insert or replace into meta(k,v) values('comms','comms')"
  eq (← stop t "comms") Json.null

def test_context_too_high_says_hand_off (t : T) : IO Unit := do
  t.agent "a"; claim t "a"
  let tr := t.d ++ "/c.jsonl"
  put tr ((json% {"type": "assistant", "message": {"usage": {"input_tokens": 600000}}}).compress ++ "\n")
  let r ← stop t "a" (json% {"transcript_path": $tr})
  has r "hand off"; hasnt r "(a) finish"

def test_cap_two_blocks_per_chain_then_allow_and_tell_comms (t : T) : IO Unit := do
  t.agent "a"; t.agent "comms"; claim t "a"
  discard <| t.q "insert or replace into meta(k,v) values('comms','comms')"
  has (← stop t "a") "claim held"
  has (← stop t "a" (json% {"stop_hook_active": true})) "claim held"
  eq (← stop t "a" (json% {"stop_hook_active": true})) Json.null
  eq (← t.q "select 1 x from event where kind='stop-cap'").size 1
  has (← t.sw "comms" ["read"]).stdout "stop hook let it go"
  has (← stop t "a") "claim held"  -- a new chain blocks again

def tests : List Case := [
  ("test_endable_stops_through", test_endable_stops_through),
  ("test_claim_blocks_with_the_three_ways_out", test_claim_blocks_with_the_three_ways_out),
  ("test_lock_blocks", test_lock_blocks),
  ("test_blocked_task_and_stay_allow", test_blocked_task_and_stay_allow),
  ("test_release_then_stop_is_endable", test_release_then_stop_is_endable),
  ("test_dirty_worktree_lists_files", test_dirty_worktree_lists_files),
  ("test_own_background_job_allows_but_swarm_wait_does_not", test_own_background_job_allows_but_swarm_wait_does_not),
  ("test_error_turn_allows", test_error_turn_allows),
  ("test_comms_is_exempt", test_comms_is_exempt),
  ("test_context_too_high_says_hand_off", test_context_too_high_says_hand_off),
  ("test_cap_two_blocks_per_chain_then_allow_and_tell_comms", test_cap_two_blocks_per_chain_then_allow_and_tell_comms)]

end SwarmLean.Tests.Cli.Stop
