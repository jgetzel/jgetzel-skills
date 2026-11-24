namespace SwarmLean.Cmd.Tasks

/-! The `-h` texts of task, rules and board, as argparse prints them from main.lua's parser. -/

/-- `swarm task -h`. -/
def helpTask : String :=
  "Usage: swarm task [-h] <command> ...\n\nOptions:\n   -h, --help            Show this help message and exit.\n\nCommands:\n   add\n   priority\n   after\n   claim\n   renew\n   show\n   done\n   land\n   unland\n   block\n   unblock\n   release\n   edit\n   label\n   drop\n   backlog\n   ready\n   assign"

/-- `swarm task add -h`. -/
def helpTaskAdd : String :=
  "Usage: swarm task add ([--body <body>] | [--body-file <body_file>])\n       [-h] [--after <after>] [--model <model>]\n       [--effort {low,medium,high,xhigh,max}] [-p <priority>]\n       [--base <base>] [--label <label>]\n       ([--repo <repo>] | [--no-repo]) <title>\n\nArguments:\n   title\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --body <body>         default: \n   --body-file <body_file>\n                         the body is this file's text; - reads stdin\n   --after <after>       ids it waits on: 3 or 3,5\n   --model <model>\n   --effort {low,medium,high,xhigh,max}\n           -p <priority>,\n   --priority <priority>\n                         urgent, high, medium, low or none (default medium)\n   --base <base>         branch its work lands on (default: .claude/swarm.json base, else main)\n   --label <label>       labels: ui or ui,herdr; an agent done with a task is offered startable ones sharing one\n   --repo <repo>         a repo it touches (repeatable; default: the folder's): a worktree in each when spawned\n   --no-repo             it touches no repo: no worktree, and only a claim or `spawn --task` staffs it"

/-- `swarm task priority -h`. -/
def helpTaskPriority : String :=
  "Usage: swarm task priority [-h] <id> <priority>\n\nArguments:\n   id\n   priority\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm task after -h`. -/
def helpTaskAfter : String :=
  "Usage: swarm task after [-h] <id> [<deps>]\n\nArguments:\n   id\n   deps\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm task claim -h`. -/
def helpTaskClaim : String :=
  "Usage: swarm task claim [-h] [--lease <lease>] [--force] <id>\n\nprints the body, and the notes held for the task's next owner (`swarm post '#<id>'`)\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --lease <lease>       default: 2h\n   --force               claim a Backlog task, or one assigned to another (the communicator or the user only)"

/-- `swarm task backlog -h`. -/
def helpTaskBacklog : String :=
  "Usage: swarm task backlog [-h] --note <note> <id>\n\nMoves a Ready task to Backlog: auto-spawn and agents asking for work skip it, and `task claim` refuses it\nwithout --force, until the communicator or the user runs `task ready`.\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --note <note>         what the task waits for"

/-- `swarm task ready -h`. -/
def helpTaskReady : String :=
  "Usage: swarm task ready [-h] <id>\n\nMoves a Backlog task to the end of Ready (the communicator or the user only).\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm task assign -h`. -/
def helpTaskAssign : String :=
  "Usage: swarm task assign [-h] [--none] <id> [<who>]\n\nReserves a Ready or Backlog task for an agent or a person (`human`) without claiming it: auto-spawn and the\npool skip it, and a claim by anyone else fails without --force. The communicator or the user only.\n\nArguments:\n   id\n   who\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --none                clear the assignee"

/-- `swarm task hold -h` (gone: it fails naming `task backlog`). -/
def helpTaskHold : String :=
  "Usage: swarm task hold [-h] <id>\n\ngone: `swarm task backlog <id> --note …`"

/-- `swarm task unhold -h` (gone: it fails naming `task ready`). -/
def helpTaskUnhold : String :=
  "Usage: swarm task unhold [-h] <id>\n\ngone: `swarm task ready <id>`"

/-- `swarm queue -h`. -/
def helpQueue : String :=
  "Usage: swarm queue [-h] [add <id>... [--front | --before <id> | --after <id>] | rm <id>...]\n\nReady is one ordered list: the order auto-spawn staffs in, after main red tasks. Priority never reorders it.\nWith no action: Ready in order, each with whether it is startable now, then the Backlog ids. add moves ids to the\nend (several keep their order), or with --front, --before or --after to that place; rm moves them to the end.\nAny agent may move a task to the end; the other moves are the communicator's or the user's.\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --front               move to the front\n   --before <id>         add before this Ready or Backlog task\n   --after <id>          add after this Ready or Backlog task"

/-- `swarm task renew -h`. -/
def helpTaskRenew : String :=
  "Usage: swarm task renew [-h] [--lease <lease>] <id>\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --lease <lease>       default: 2h"

/-- `swarm task show -h`. -/
def helpTaskShow : String :=
  "Usage: swarm task show [-h] [--json] <id>\n\nthe task, its edits and its notes (`swarm post '#<id>'`)\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --json                the row and its notes as JSON"

/-- `swarm task done -h`. -/
def helpTaskDone : String :=
  "Usage: swarm task done [-h] --evidence <evidence> <id>\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --evidence <evidence>\n                         a landing task's: a commit on the task's base (its lander closes it)"

/-- `swarm task land -h`. -/
def helpTaskLand : String :=
  "Usage: swarm task land [-h] --sha <sha> [--lander <lander>] <id>\n\nYour claimed task's work passed its checks at <sha>: hand it to a lander. The task is landing: no longer yours\n(take the next task or go idle) and not claimable; its --after dependants wait until it is done. Its lander, an\nagent with role lander or the communicator closes it with `task done --evidence <sha on its base>` or `task unland`.\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --sha <sha>           the commit that passed its checks\n   --lander <lander>     the agent to land it (told now); default: any lander"

/-- `swarm task unland -h`. -/
def helpTaskUnland : String :=
  "Usage: swarm task unland [-h] --why <why> <id>\n\nA lander gives a task In Review back: Ready again at priority High (Urgent stays), with why appended to its body;\nits former owner, if live, and the communicator are told.\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --why <why>           why it did not land"

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

/-- `swarm task label -h`. -/
def helpTaskLabel : String :=
  "Usage: swarm task label [-h] <id> [<labels>] ...\n\nArguments:\n   id\n   labels                its labels from now on: ui herdr or ui,herdr; none clears them\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm task drop -h`. -/
def helpTaskDrop : String :=
  "Usage: swarm task drop [-h] [--duplicate-of <duplicate_of>] [--note <note>] <id>\n\nCancels the task; with --duplicate-of it is a Duplicate of that task.\n\nArguments:\n   id\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --duplicate-of <duplicate_of>\n                         the original task\n   --note <note>         why"

/-- `swarm rules -h`. -/
def helpRules : String :=
  "Usage: swarm rules [-h] <command> ...\n\nOptions:\n   -h, --help            Show this help message and exit.\n\nCommands:\n   show\n   set"

/-- `swarm rules show -h`. -/
def helpRulesShow : String :=
  "Usage: swarm rules show [-h]\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm rules set -h`. -/
def helpRulesSet : String :=
  "Usage: swarm rules set [-h] <text> [<text>] ...\n\nSets the rules of the swarm this command acts on: every spawn's first message carries them.\n\nArguments:\n   text\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- `swarm board -h`. -/
def helpBoard : String :=
  "Usage: swarm board [-h] [--all] [--json]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --all\n   --json                the Board's snapshot, as `swarm state --json --view board` prints it"

/-- `swarm  -h`. -/
def helpRoot : String :=
  "Usage: swarm [-h] <command> ...\n\nOptions:\n   -h, --help            Show this help message and exit.\n\nCommands:\n   spawn\n   join\n   end                   communicator: end an agent's terminal (not its worktree); checks it is idle with work landed\n   endable               exit 0 if nothing keeps the agent from being ended by watchd, else 1\n   leave\n   post\n   read\n   wait\n   ci\n   task\n   rules\n   board\n   who\n   role\n   stay\n   nudge                 type one fixed line into an agent's terminal: read your messages and continue\n   limits\n   away\n   lock\n   unlock\n   machine\n   cost\n   run\n   state\n   watch\n   watchd\n   hook"

end SwarmLean.Cmd.Tasks
