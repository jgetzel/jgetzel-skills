namespace SwarmLean.Cmd.Msgs

/-! The `-h` texts of post, read, wait and nudge, as argparse prints them from main.lua's parser. -/

/-- `swarm post -h`. -/
def helpPost : String :=
  "Usage: swarm post [-h] [--urgent] <to> <text> [<text>] ...\n\nArguments:\n   to\n   text\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --urgent"

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
