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
  "Usage: swarm run [-h] [--on <on>] [--cores <cores>] [--mem <mem>]\n       [--env NAME[=VAL]]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --on <on>             an hc machine (`hc machine ls`); default: here, then run.machines in .claude/swarm.json\n   --cores <cores>       cores to claim, or `all` the cap (default: from `swarm cost` history, else 2)\n   --mem <mem>           GiB to claim (default: the history's peak plus a quarter, else 2)\n   --env NAME[=VAL]      also pass this variable (repeatable)\n\nClaims the cores and memory on a machine (waiting for room, in order), runs the command there and releases them.\nThe job gets SWARM_CORES, SWARM_MEM_KB, MAKEFLAGS=-j<cores>, CARGO_BUILD_JOBS and NIX_BUILD_CORES."

/-- `swarm compute -h`. -/
def helpCompute : String :=
  "Usage: swarm compute [-h] [--json] [--cores <cores>] [--mem <mem>]\n       [<words>] ...\n\nArguments:\n   words                 cap <machine|here>, off <machine|here> or on <machine|here>; none: the claims on every machine\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --json\n   --cores <cores>       cap: cores `swarm run` may claim, N or all\n   --mem <mem>           cap: GiB `swarm run` may claim, or all"

/-- `swarm state -h`. -/
def helpState : String :=
  "Usage: swarm state [-h] --json\n       [--view {activity,agents,board,graph,overview,summary,swarms,system}]\n       [--agent <agent>] [--task <task>] [--before <before>]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --json\n   --view {activity,agents,board,graph,overview,summary,swarms,system}\n                         only what that panel view shows (default: everything);\n                         swarms: every swarm on this machine whose watchd runs;\n                         graph: also every task with a dependency or that is one\n   --agent <agent>       also the detail pane's messages and events for this agent\n   --task <task>         also that task's body, events and the messages that name it\n   --before <before>     the next page: board, done and dropped tasks numbered below it;\n                         agents, ended agents that ended before it (unix seconds)"

/-- `swarm watch -h`. -/
def helpWatch : String :=
  "Usage: swarm watch [-h] [--tail <tail>] [--once]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --tail <tail>\n   --once"

end SwarmLean.Cmd
