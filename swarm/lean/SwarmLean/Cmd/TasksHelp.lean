namespace SwarmLean.Cmd.Tasks

/-! The `-h` texts of task, rules and board, as argparse prints them from main.lua's parser. -/

/-- `swarm task -h`. -/
def helpTask : String :=
  "Usage: swarm task [-h] <command> ...\n\nOptions:\n   -h, --help            Show this help message and exit.\n\nCommands:\n   add\n   priority\n   after\n   claim\n   renew\n   show\n   done\n   block\n   unblock\n   release\n   edit\n   drop\n   hold\n   unhold"

/-- `swarm task add -h`. -/
def helpTaskAdd : String :=
  "Usage: swarm task add ([--body <body>] | [--body-file <body_file>])\n       [-h] [--after <after>] [--model <model>]\n       [--effort {low,medium,high,xhigh,max}] [-p <priority>]\n       [--base <base>] <title>\n\nArguments:\n   title\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --body <body>         default: \n   --body-file <body_file>\n                         the body is this file's text; - reads stdin\n   --after <after>       ids it waits on: 3 or 3,5\n   --model <model>\n   --effort {low,medium,high,xhigh,max}\n           -p <priority>,\n   --priority <priority>\n                         priority 0-3, lower first (default 2)\n   --base <base>         branch its work lands on (default: .claude/swarm.json base, else main)"

/-- `swarm task priority -h`. -/
def helpTaskPriority : String :=
  "Usage: swarm task priority [-h] <id> <priority>\n\nArguments:\n   id\n   priority\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm task after -h`. -/
def helpTaskAfter : String :=
  "Usage: swarm task after [-h] <id> [<deps>]\n\nArguments:\n   id\n   deps\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm task claim -h`. -/
def helpTaskClaim : String :=
  "Usage: swarm task claim [-h] [--lease <lease>] [--force] <id>\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --lease <lease>       default: 2h\n   --force               claim a held task (the communicator or the user only)"

/-- `swarm task hold -h`. -/
def helpTaskHold : String :=
  "Usage: swarm task hold [-h] --why <why> <id>\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --why <why>           what the task waits for; until `task unhold`, neither auto-spawn nor an agent asking for\n                         work takes it, and `task claim` refuses it"

/-- `swarm task unhold -h`. -/
def helpTaskUnhold : String :=
  "Usage: swarm task unhold [-h] <id>\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm queue -h`. -/
def helpQueue : String :=
  "Usage: swarm queue [-h] [add <id>... [--front | --before <id> | --after <id>] | rm <id>...]\n\nThe order auto-spawn staffs in, after main red tasks and before priority. With no action: the queue in order,\neach with whether it is startable now. add appends (several ids keep their order; a queued id moves); rm takes ids out.\nAny agent may append and move or remove what it queued; --front, --before, --after and changing another's\nentries are the communicator's or the user's. A task done or dropped leaves the queue.\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --front               add at the front\n   --before <id>         add before this queued task\n   --after <id>          add after this queued task"

/-- `swarm task renew -h`. -/
def helpTaskRenew : String :=
  "Usage: swarm task renew [-h] [--lease <lease>] <id>\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --lease <lease>       default: 2h"

/-- `swarm task show -h`. -/
def helpTaskShow : String :=
  "Usage: swarm task show [-h] <id>\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm task done -h`. -/
def helpTaskDone : String :=
  "Usage: swarm task done [-h] --evidence <evidence> <id>\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --evidence <evidence>"

/-- `swarm task block -h`. -/
def helpTaskBlock : String :=
  "Usage: swarm task block [-h] <id> <question>\n\nArguments:\n   id\n   question\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm task unblock -h`. -/
def helpTaskUnblock : String :=
  "Usage: swarm task unblock [-h] [--answer <answer>] <id>\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --answer <answer>     default: "

/-- `swarm task release -h`. -/
def helpTaskRelease : String :=
  "Usage: swarm task release [-h] [--after <after>] <id>\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --after <after>       ids it now waits on: 3 or 3,5"

/-- `swarm task edit -h`. -/
def helpTaskEdit : String :=
  "Usage: swarm task edit\n       ([--body <body>] | [--body-file <body_file>] | [--append <append>])\n       [-h] [--title <title>] [--model <model>]\n       [--effort {low,medium,high,xhigh,max}] [--urgent] <id>\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --title <title>\n   --body <body>\n   --body-file <body_file>\n                         replace the body with this file's text; - reads stdin\n   --append <append>     add this text to the end of the body\n   --model <model>\n   --effort {low,medium,high,xhigh,max}\n   --urgent              make the owner's notice urgent"

/-- `swarm task drop -h`. -/
def helpTaskDrop : String :=
  "Usage: swarm task drop [-h] <id>\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm rules -h`. -/
def helpRules : String :=
  "Usage: swarm rules [-h] <command> ...\n\nOptions:\n   -h, --help            Show this help message and exit.\n\nCommands:\n   show\n   set"

/-- `swarm rules show -h`. -/
def helpRulesShow : String :=
  "Usage: swarm rules show [-h]\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm rules set -h`. -/
def helpRulesSet : String :=
  "Usage: swarm rules set [-h] <text> [<text>] ...\n\nArguments:\n   text\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm board -h`. -/
def helpBoard : String :=
  "Usage: swarm board [-h] [--all]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --all"

/-- `swarm  -h`. -/
def helpRoot : String :=
  "Usage: swarm [-h] <command> ...\n\nOptions:\n   -h, --help            Show this help message and exit.\n\nCommands:\n   spawn\n   join\n   end                   communicator: end an agent's terminal (not its worktree); checks it is idle with work landed\n   endable               exit 0 if nothing keeps the agent from being ended by watchd, else 1\n   leave\n   post\n   read\n   wait\n   ci\n   task\n   rules\n   board\n   who\n   role\n   stay\n   nudge                 type one fixed line into an agent's terminal: read your messages and continue\n   limits\n   away\n   lock\n   unlock\n   machine\n   cost\n   run\n   state\n   watch\n   watchd\n   hook"

end SwarmLean.Cmd.Tasks
