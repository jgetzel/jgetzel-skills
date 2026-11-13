namespace SwarmLean.Cmd.Agents

/-! The `-h` texts of the agent and machine commands, as argparse prints them from main.lua's parser. -/

/-- `swarm spawn -h`. -/
def helpSpawn : String :=
  "Usage: swarm spawn [-h] [--model <model>]\n       [--effort {low,medium,high,xhigh,max}] [--stay <stay>]\n       [--task <task>] [--role <role>] [--attach <attach>] <name>\n       [<task>] ...\n\nArguments:\n   name\n   task\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --model <model>       default: sonnet\n   --effort {low,medium,high,xhigh,max}\n                         claude --effort for the new agent (default: its settings)\n   --stay <stay>         what the new agent waits for: watchd won't end it while it stays\n   --task <task>         claim this board task for the new agent before launching\n   --role <role>         the new agent's role label (`swarm role`)\n   --attach <attach>     start it read-only in this swarm workspace instead of making it a worktree"

/-- `swarm join -h`. -/
def helpJoin : String :=
  "Usage: swarm join [-h] [--model <model>] [--takeover] [<name>]\n\nArguments:\n   name\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --model <model>\n   --takeover            move a live binding of this name to this terminal"

/-- `swarm leave -h`. -/
def helpLeave : String :=
  "Usage: swarm leave [-h] [<name>]\n\nArguments:\n   name\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm end -h`. -/
def helpEnd : String :=
  "Usage: swarm end [-h] [--force] <agent>\n\ncommunicator: end an agent's terminal (not its worktree); checks it is idle with work landed\n\nArguments:\n   agent\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --force               skip the checks"

/-- `swarm endable -h`. -/
def helpEndable : String :=
  "Usage: swarm endable [-h] [--why] [<agent>]\n\nexit 0 if nothing keeps the agent from being ended by watchd, else 1\n\nArguments:\n   agent\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --why                 print every reason"

/-- `swarm who -h`. -/
def helpWho : String :=
  "Usage: swarm who [-h]\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm role -h`. -/
def helpRole : String :=
  "Usage: swarm role [-h] [<text>] ...\n\nArguments:\n   text\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm stay -h`. -/
def helpStay : String :=
  "Usage: swarm stay [-h] [--end] [<text>] ...\n\nArguments:\n   text\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --end                 clear it: judged as any agent again; `--end NAME` clears NAME's (human or the communicator)"

/-- `swarm limits -h`. -/
def helpLimits : String :=
  "Usage: swarm limits [-h] [--min <min>] [--max <max>]\n       [--queue-only {on,off}] [--ctx-nudge <ctx_nudge>]\n       [--ctx-compact <ctx_compact>] [--compact-stayers {on,off}]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --min <min>           auto-spawn number: watchd staffs tasks until this many agents are live\n   --max <max>           agent max: `swarm spawn` refuses at this many live agents\n   --queue-only {on,off}\n                         on: auto-spawn staffs only `swarm queue` (and main red tasks); unqueued tasks are\n                         backlog (default off)\n   --ctx-nudge <ctx_nudge>\n                         context in tokens from which watchd nudges an agent to compact itself and claims are\n                         refused (default 325000; 0: off)\n   --ctx-compact <ctx_compact>\n                         context in tokens from which watchd compacts an idle agent (default 400000; 0: off)\n   --compact-stayers {on,off}\n                         on: the communicator and agents with a stay are compacted too, not only nudged\n                         (default off)"

/-- `swarm away -h`. -/
def helpAway : String :=
  "Usage: swarm away [-h] [--back] [<note>] ...\n\nArguments:\n   note\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --back                the user is back: print what waits for them"

/-- `swarm machine -h`. -/
def helpMachine : String :=
  "Usage: swarm machine [-h]\n\nOptions:\n   -h, --help            Show this help message and exit."

end SwarmLean.Cmd.Agents
