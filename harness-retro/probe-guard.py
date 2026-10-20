#!/usr/bin/env python3
"""PreToolUse guard for harness-retro probe agents: keep a replay inside its checkout.

  probe-guard.py WORKTREE MAIN_REPO      (hook; event JSON on stdin)
  probe-guard.py --selftest

Allows a fixed set of local tools. Denies anything that reaches outside the
checkout: pushes, PRs, ssh, herdr, messages to other agents, shared git refs,
writes outside the worktree and /tmp, and any command naming the main repo.
"""
import json, os, re, sys

TOOLS = {"Read", "Write", "Edit", "MultiEdit", "NotebookEdit", "Bash", "Glob", "Grep", "LS", "ToolSearch",
         "Skill", "TodoWrite", "Task", "Agent", "Monitor", "TaskStop", "TaskOutput", "BashOutput", "KillShell",
         "WebFetch", "WebSearch"}
# ponytail: a denylist on command text, not a sandbox; Bash can still write outside via a script it wrote.
DENY = re.compile(r"\bgit\s+(push|worktree|tag|update-ref|stash|branch\s+(-[dDmMcC]\b|[^-\s])|checkout\s+-[bB]|switch\s+-[cC])"
                  r"|\bgh\s+(pr|issue|release|repo|api|workflow|run\s+(rerun|cancel))\b"
                  r"|\b(ssh|scp|rsync|herdr|pkill|killall)\b|\b(npm|cargo|uv)\s+publish\b|\bdocker\s+push\b"
                  r"|\bcurl\b[^|;&]*-X\s*(POST|PUT|PATCH|DELETE)")


def verdict(d, wt, main):
    tool, inp = d.get("tool_name", ""), d.get("tool_input") or {}
    if tool not in TOOLS:
        return f"{tool} reaches outside this sandboxed replay"
    if inp.get("isolation"):
        return "worktree isolation creates shared git refs; work in this checkout"
    cmd = inp.get("command") or ""
    if cmd:
        m = DENY.search(cmd)
        if m:
            return f"`{m.group(0).strip()}` leaves this sandboxed replay"
        mains = (main, main.replace(os.path.expanduser("~"), "~", 1))
        if any(re.search(re.escape(p) + r"(/|\s|$|['\"])", cmd) for p in mains):
            return f"{main} is the live repo; use this checkout ({wt})"
    path = inp.get("file_path") or inp.get("notebook_path")
    if path and tool not in ("Read", "Glob", "Grep", "LS"):
        p = os.path.realpath(os.path.expanduser(path))
        if not any(p == r or p.startswith(r + os.sep) for r in (os.path.realpath(wt), "/tmp")):
            return f"write to {path} is outside this checkout"
    return None


def selftest():
    wt, main = "/w/.r-worktrees/probe-1-a", os.path.expanduser("~/r")
    ok = lambda t, **i: verdict({"tool_name": t, "tool_input": i}, wt, main) is None
    assert not ok("Bash", command="git commit -m 'ssh fix'")  # matches inside quotes too, deliberately
    assert ok("Bash", command="just test && git commit -am wip")
    assert not ok("Bash", command="git push origin HEAD")
    assert not ok("Bash", command="bash -c 'gh pr create'")
    assert not ok("Bash", command="git branch -D other")
    assert ok("Bash", command="git branch --show-current")
    assert not ok("Bash", command=f"cd {main} && ls")
    assert not ok("Bash", command="git -C ~/r log")
    assert ok("Bash", command="ls ~/rx")
    assert not ok("Monitor", command="ssh desktop tail -F log")
    assert not ok("SendMessage", to="wf-ml", message="hi")
    assert not ok("Agent", prompt="x", isolation="worktree")
    assert ok("Write", file_path=wt + "/a.py")
    assert ok("Write", file_path="/tmp/x")
    assert not ok("Write", file_path=os.path.expanduser("~/.claude/projects/r/memory/m.md"))
    assert ok("Read", file_path="/etc/hosts")
    print("probe-guard selftest ok")


if __name__ == "__main__":
    if sys.argv[1:] == ["--selftest"]:
        sys.exit(selftest())
    why = verdict(json.load(sys.stdin), sys.argv[1], sys.argv[2])
    if why:
        print(f"Blocked by harness-retro probe-guard: {why}. This is a sandboxed replay; "
              "note what you would have done and continue locally.", file=sys.stderr)
        sys.exit(2)
