namespace SwarmLean.Cmd

/-! The `-h` texts of ci, cost, run, state and watch, as argparse prints them from main.lua's parser. -/

/-- `swarm ci -h`. -/
def helpCi : String :=
  "Usage: swarm ci [-h] [--wait] [--timeout <timeout>] [--poll <poll>]\n       [<sha>]\n\nArguments:\n   sha                   default: HEAD\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --wait                block until a finished run includes it\n   --timeout <timeout>\n   --poll <poll>"

/-- `swarm cost -h`. -/
def helpCost : String :=
  "Usage: swarm cost [-h] [--top] [--repo <repo>] [--all-repos]\n       [<words>] ...\n\nArguments:\n   words\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --top\n   --repo <repo>\n   --all-repos"

/-- `swarm pr -h`. -/
def helpPr : String :=
  "Usage: swarm pr [-h] <command> ...\n\nCommands:\n   merge-when-green      squash-merge PRs once their checks are green\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm pr merge-when-green -h`. -/
def helpPrMergeWhenGreen : String :=
  "Usage: swarm pr merge-when-green [-h] [--every <every>] [--polls <polls>] <prs> ...\n\nArguments:\n   prs\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --every <every>       seconds between polls (default 180)\n   --polls <polls>       polls before giving up (default 40: 2 h)\n\nSquash-merges each PR whose head has all checks COMPLETED with SUCCESS or SKIPPED and is MERGEABLE, passing that head's sha\nto --match-head-commit, so a later push is not merged untested. Exits 0 when all are merged, else 1 with what is left."

/-- `swarm run -h`. -/
def helpRun : String :=
  "Usage: swarm run [-h] [--no-devshell] [--detach] [--on <on>] [--cores <cores>] [--mem <mem>]\n       [--env NAME[=VAL]]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --no-devshell         run the command as it is, without entering the flake's dev shell
   --detach              return once the job is claimed and started (\"job jN started on …\"), and run the rest in the background: its end line (plus the log\'s tail when the exit is not 0) comes as a message to you, else to its task, else to the communicator; `swarm stay --until job:N` waits for it\n   --on <on>             an hc machine (`hc machine ls`); default: here, then run.machines in .claude/swarm.json\n   --cores <cores>       cores to claim (default: from `swarm cost` history, else 2), or `all`: the whole machine, alone\n                         (waits for no other claim, no reservation and no unclaimed use; not with --mem)\n   --mem <mem>           GiB to claim (default: the history's peak plus a quarter, else 2); given explicitly it also caps the\n                         job at that many GiB with swap off on Linux (systemd user scope), a defaulted one only reserves;\n                         macOS has no cap\n   --env NAME[=VAL]      also pass this variable (repeatable)\n\nClaims the cores and memory on a machine (waiting for room, in order), runs the command there at the lowest CPU and I/O\npriority and releases them. A command with history carries its 90th-percentile wall time (`~5m`), which lets it start\nbefore an older waiter that cannot start sooner; one without waits its turn.\nThe job gets SWARM_CORES, SWARM_MEM_KB, MAKEFLAGS=-j<cores>, CARGO_BUILD_JOBS and NIX_BUILD_CORES, and SWARM_JOB_ID and\nSWARM_JOB_MACHINE (the job's id and machine). A `swarm run` started inside a local job (SWARM_JOB_ID set, the same machine, no --on)\nclaims nothing: it runs inside the parent's claim with the parent's SWARM_CORES, recorded as a job with a \"parent\"."

/-- `swarm job -h`. -/
def helpJob : String :=
  "Usage: swarm job [-h] <command> ...\n\nCommands:\n   record                record a job that ran elsewhere, or inside another job's claim\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm job record -h`. -/
def helpJobRecord : String :=
  "Usage: swarm job record [-h] --who <who> [--task <task>] [--parent <parent>] [--machine <machine>]\n       [--cores <cores>] [--start <start>] --wall <wall> [--cpu <cpu>] [--peak-kb <peak-kb>]\n       --exit <exit> [--log <log>] -- <cmd…>\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --who <who>           the agent the job is for\n   --task <task>         its task (default: who's claimed task)\n   --parent <parent>     the job whose claim it ran in, jN or N (default: $SWARM_JOB_ID)\n   --machine <machine>   where it ran (default: this machine)\n   --cores <cores>       cores it had\n   --start <start>       when it started, unix seconds (default: now minus --wall)\n   --wall <wall>         seconds it took\n   --cpu <cpu>           CPU seconds it used (0 or none: no reading)\n   --peak-kb <peak-kb>   its peak memory in KiB (0 or none: no reading)\n   --exit <exit>         its exit code, or lost\n   --log <log>           a file copied to jobs/<jid>/log\n\nA job that ran inside another job's claim (the timing queue's) gets a job id, job-start and job-end events and a `swarm cost`\nrow of its own, so `swarm run` sizes the next run of the same command from it. Claims nothing, runs nothing. Prints `recorded jN`."

/-- `swarm compute -h`. -/
def helpCompute : String :=
  "Usage: swarm compute [-h] [--json] [--cores <cores>] [--mem <mem>] [--id <id>]\n       [--who <who>] [--est <est>] [--ttl <ttl>] [--pid <pid>] [--owner <owner>]\n       [<words>] ... [-- <cmd>...]\n\nArguments:\n   words                 cap <machine|here>, reserve <machine|here> <cores>, off <machine|here> or on <machine|here>, queue add <machine|here> (with --id, --who and the command after --) or queue rm <machine|here> <id>;\n                         one machine (here or hc's name): its claims only; none: the claims on every machine\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --json\n   --cores <cores>       cap: cores `swarm run` may claim, N or all\n   --mem <mem>           cap: GiB `swarm run` may claim, or all; reserve: GiB kept for you (default 0)\n   --id <id>             queue add: the entry's id; --who <who>: who it is for; --est <est>: seconds it will take; --ttl <ttl>: seconds\n                         until it lapses unless renewed (default 900); --pid <pid>: instead, lapse when this local pid is gone;\n                         --owner <owner>: what keeps it (default the user)\n\nqueue add shows a waiting job under the machine, display only: it holds no cores and no place in line; add it again to renew it.\n\ncap is the standing limit; reserve is the temporary one, the part of the machine kept for you now (`reserve here 0` lifts it):\nclaims wait for the rest, and a larger one waits without holding back smaller ones."

/-- `swarm state -h`. -/
def helpState : String :=
  "Usage: swarm state [-h] --json\n       [--view {activity,agents,board,graph,overview,summary,swarms,system}]\n       [--agent <agent>] [--task <task>] [--before <before>]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --json\n   --view {activity,agents,board,graph,overview,summary,swarms,system}\n                         only what that panel view shows (default: everything);\n                         swarms: every swarm on this machine whose watchd runs;\n                         graph: also every task with a dependency or that is one\n   --agent <agent>       also the detail pane's messages and events for this agent\n   --task <task>         also that task's body, events and the messages that name it\n   --before <before>     the next page: board, done and dropped tasks numbered below it;\n                         agents, ended agents that ended before it (unix seconds)"

/-- `swarm watch -h`. -/
def helpWatch : String :=
  "Usage: swarm watch [-h] [--tail <tail>] [--once]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --tail <tail>\n   --once"

end SwarmLean.Cmd
