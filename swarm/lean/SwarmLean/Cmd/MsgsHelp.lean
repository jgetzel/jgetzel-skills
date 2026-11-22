namespace SwarmLean.Cmd.Msgs

/-! The `-h` texts of post, read, wait and nudge, as argparse prints them from main.lua's parser. -/

/-- `swarm post -h`. -/
def helpPost : String :=
  "Usage: swarm post [-h] [--urgent] <to> <text> [<text>] ...\n\nArguments:\n   to                    an agent of any swarm, @all (your swarm), @<swarm> (its agents), or '#<N>'\n                         (task:<N>): a note on task N for whoever holds it. A result for a task goes to '#N',\n                         not to an agent who may end: its live owner gets it now, else its next `task claim`\n                         prints it; on a done task, whoever did it, else the communicator\n   text\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --urgent"

/-- `swarm read -h`. -/
def helpRead : String :=
  "Usage: swarm read [-h]\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm wait -h`. -/
def helpWait : String :=
  "Usage: swarm wait [-h] [--me <me>] [--timeout <timeout>]\n       [--poll <poll>]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --me <me>\n   --timeout <timeout>\n   --poll <poll>"

/-- `swarm nudge -h`. -/
def helpNudge : String :=
  "Usage: swarm nudge [-h] <agent>\n\ntype one fixed line into an agent's terminal: read your messages and continue\n\nArguments:\n   agent\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm compact -h`. -/
def helpCompact : String :=
  "Usage: swarm compact [-h] [--keep <keep>]\n\ntype `/compact <what to keep>` into your own terminal; it runs when this turn ends\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --keep <keep>         more to keep, after your task, worktree and branch"

end SwarmLean.Cmd.Msgs
