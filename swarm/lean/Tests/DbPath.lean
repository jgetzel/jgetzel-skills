import SwarmLean.DbPath

/-! DbPath's asserts: which db a command opens, and what it says outside a repo with none. -/

namespace SwarmLean.Tests.DbPath
open SwarmLean.DbPath

-- $SWARM_DB first, then the repo, then this terminal's communicator label; the empty string is unset
#guard choose (some "/e.db") (some "/r/.git") (some "/l.db") == some "/e.db"
#guard choose (some "") (some "/r/.git\n") (some "/l.db") == some "/r/.git/swarm/swarm.db"
#guard choose none (some "") (some "/l.db") == some "/l.db"
#guard choose none none none == none && choose none none (some "") == none
#guard repoOf "/a/pai-web/.git/swarm/swarm.db" == some "/a/pai-web" && repoOf "/a/swarm.db" == none
#guard repoOf "/.git/swarm/swarm.db" == none
-- the registry's swarms under the cwd, then the repos below it, each db once
#guard candidates "/n" [("/n/a", "/n/a/.git/swarm/swarm.db"), ("/x/b", "/x/b.db"), ("/na", "/na.db")]
    [("/n/a", "/n/a/.git/swarm/swarm.db"), ("/n/c", "/n/c/.git/swarm/swarm.db")]
  == [("/n/a", "/n/a/.git/swarm/swarm.db"), ("/n/c", "/n/c/.git/swarm/swarm.db")]
#guard noDbText "/n" [("/n/a", "/n/a.db")] ==
  "not in a git repo and SWARM_DB is unset; swarms under /n:\n  a: export SWARM_DB=/n/a.db\ncd into one, or export its SWARM_DB"

end SwarmLean.Tests.DbPath
