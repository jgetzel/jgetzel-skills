import Tests.Cli.Spawn

/-! A row that does not decode refuses the command that reads it, naming its table, key cells and the decoder's reason
(board #1811): nothing works on top of a malformed row. -/

namespace SwarmLean.Tests.Cli.Refuse
open SwarmLean.Tests.Cli
open SwarmLean.Sqlite (Val)

/-- Runs `args` as a: it exits non-zero and says `want`. -/
def refuses (t : T) (args : List String) (want : String) : IO Unit := do
  let r ← t.sw "a" args { ok := false }
  if r.code == 0 then fail s!"{args} exited 0: {r.stdout}"
  has (r.stdout ++ r.stderr) want

def test_refuse_task_row (t : T) : IO Unit := do
  t.agent "a"
  t.sw_ "a" ["task", "add", "t1"]
  t.q_ "update task set state='clamed' where id=1"
  refuses t ["task", "show", "1"] "swarm.db: task #1: unknown task state 'clamed'"
  refuses t ["board"] "swarm.db: task #1: unknown task state 'clamed'"
  refuses t ["state", "--json", "--view", "swarms"] "swarm.db: task #1: unknown task state 'clamed'"

def test_refuse_agent_row (t : T) : IO Unit := do
  t.agent "a"
  t.agent "b"
  t.q_ "update agent set status='bogus' where name='b'"
  refuses t ["state", "--json", "--view", "swarms"] "swarm.db: agent b: "
  
def test_refuse_msg_row (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  t.sw_ "b" ["post", "a", "hi"]
  t.q_ "update msg set ts='yesterday'"
  refuses t ["read"] "swarm.db: msg #"

def test_refuse_lock_row (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  t.sw_ "b" ["lock", "x.txt"]
  t.q_ "update lock set since='soon'"
  refuses t ["lock", "y.txt"] "swarm.db: lock "

def tests : List Case := [
  ("test_refuse_task_row", test_refuse_task_row),
  ("test_refuse_agent_row", test_refuse_agent_row),
  ("test_refuse_msg_row", test_refuse_msg_row),
  ("test_refuse_lock_row", test_refuse_lock_row)]

end SwarmLean.Tests.Cli.Refuse
