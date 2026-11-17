import SwarmLean.Util

/-! Where the db is, and what a command says when there is none: one decision for the store's connect (Real.lean) and
the commands' own reads of the path (Lib/Spawn.lean). -/

namespace SwarmLean.DbPath

/-- The db (db.dbpath): `$SWARM_DB`; else swarm/swarm.db in the git common dir of the cwd's repo; else the db this
terminal is the communicator of (its hc label `swarm.comms`, which join writes), so a communicator whose cwd is a parent
folder of several repos keeps its swarm. -/
def choose (envDb gitDir label : Option String) : Option String :=
  match py envDb with
  | some p => some p
  | none => match py (gitDir.map strip) with
    | some g => some (joinPath (joinPath g "swarm") "swarm.db")
    | none => py label

/-- The repo folder of db `p` when it is a repo's default db (`<folder>/.git/swarm/swarm.db`). -/
def repoOf (p : String) : Option String :=
  let sfx := "/.git/swarm/swarm.db"
  if p.endsWith sfx && p.length > sfx.length then some (String.ofList (p.toList.take (p.length - sfx.length))) else none

/-- What a command needing a db says with none: the swarms found under `cwd` (folder, db), each with its
`SWARM_DB`, else where to look. -/
def noDbText (cwd : String) (cands : List (String × String)) : String :=
  let head := "not in a git repo and SWARM_DB is unset"
  if cands.isEmpty then
    head ++ s!" (cwd {cwd}): cd into the swarm's repo, or export SWARM_DB=<its db>; `swarm state --json --view swarms` lists the swarms whose watchd runs or that agents joined"
  else
    let pre := if cwd.endsWith "/" then cwd else cwd ++ "/"
    let rel (f : String) : String := if f.startsWith pre then (f.drop pre.length).toString else f
    head ++ s!"; swarms under {cwd}:" ++ String.join (cands.map fun (f, d) => s!"\n  {rel f}: export SWARM_DB={d}") ++
      "\ncd into one, or export its SWARM_DB"

/-- The candidates `noDbText` lists: registry entries (folder, db) under `cwd`, then the repos right below it with a
default db, each db once, at most ten. -/
def candidates (cwd : String) (registry repos : List (String × String)) : List (String × String) :=
  let under (f : String) : Bool := f.startsWith (if cwd.endsWith "/" then cwd else cwd ++ "/")
  let all := registry.filter (under ·.1) ++ repos
  (all.foldl (fun acc c => if acc.any (·.2 == c.2) then acc else acc ++ [c]) []).take 10

end SwarmLean.DbPath
