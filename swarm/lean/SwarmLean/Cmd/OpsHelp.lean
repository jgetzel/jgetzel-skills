namespace SwarmLean.Cmd

/-! The `-h` texts of ci, cost, run, state and watch, as argparse prints them from main.lua's parser. -/

/-- `swarm ci -h`. -/
def helpCi : String :=
  "Usage: swarm ci [-h] [--wait] [--timeout <timeout>] [--poll <poll>]\n       [<sha>]\n\nArguments:\n   sha                   default: HEAD\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --wait                block until a finished run includes it\n   --timeout <timeout>\n   --poll <poll>"

/-- `swarm cost -h`. -/
def helpCost : String :=
  "Usage: swarm cost [-h] [--top] [--repo <repo>] [--all-repos]\n       [<words>] ...\n\nArguments:\n   words\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --top\n   --repo <repo>\n   --all-repos"

/-- `swarm run -h`. -/
def helpRun : String :=
  "Usage: swarm run [-h] [--on <on>] [--env NAME[=VAL]]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --on <on>             an hc machine (`hc machine ls`); default: here\n   --env NAME[=VAL]      also pass this variable (repeatable)"

/-- `swarm state -h`. -/
def helpState : String :=
  "Usage: swarm state [-h] --json\n       [--view {activity,agents,board,overview,system}]\n       [--agent <agent>] [--task <task>]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --json\n   --view {activity,agents,board,overview,system}\n                         only what that panel view shows (default: everything)\n   --agent <agent>       also the detail pane's messages and events for this agent\n   --task <task>         also that task's body, events and the messages that name it"

/-- `swarm watch -h`. -/
def helpWatch : String :=
  "Usage: swarm watch [-h] [--tail <tail>] [--once]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --tail <tail>\n   --once"

end SwarmLean.Cmd
