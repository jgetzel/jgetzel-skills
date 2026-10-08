#!/usr/bin/env python3
"""Where the time went: tool wall time from Claude Code transcripts, plus CI job time.

  time-report.py [--since 2026-10-07T08:00] [--project-dir DIR] [--top 15] [--no-ci]

Transcripts: every session in the project dir (the orchestrator and its herdr
agents share one) whose records fall after --since (default: 24 h ago). A
foreground tool call runs from tool_use to tool_result; a background Bash call
runs to its task-notification. Commands are grouped by what they ran (`just
test`, `gh pr checks`, ...), so the top rows are the optimization targets.
CI: `gh run list` in the cwd's repo, job and step durations for runs created
after --since.
"""
import argparse, glob, json, os, re, subprocess, sys
from collections import defaultdict
from datetime import datetime, timedelta, timezone

def ts(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00"))

KEYS = [("just", r"(?:^|[;&|(`]|\bflock\s+\S+|--command)\s*just\s+([\w-]+)"), ("gh", r"\bgh\s+(\w+\s+[\w-]+)"), ("nix", r"\bnix\s+(\w+)"),
        ("cabal", r"\bcabal\s+(\w+)"), ("git", r"\bgit\s+([\w-]+)"), ("herdr", r"\bherdr\s+(\w+\s+[\w-]+)"),
        ("script", r"([\w-]+\.(?:sh|py))\b")]

def key(name, inp):
    if name != "Bash":
        return name
    cmd = inp.get("command", "")
    if re.match(r"\s*(until|while|sleep)\b", cmd):
        return "bash: wait loop"
    if re.search(r"gh run watch|gh pr checks .*--watch", cmd):
        return "gh: wait for CI"
    for prefix, rx in KEYS:
        m = re.search(rx, cmd)
        if m:
            return f"{prefix} {m.group(1)}"
    return "bash: " + (cmd.split() or ["?"])[0]

def label(first_text, sid):
    # Agent briefs open "You are <name>", sometimes as pasted content.
    m = re.search(r"agent \*\*([\w-]+)\*\*", first_text) or re.search(r"^\W*(?:<pasted_content[^>]*>\s*)?You are \**([a-z][\w-]*)", first_text)
    if m:
        return m.group(1)
    if "orchestrat" in first_text:
        return "orchestrator"
    return sid[:8]

def text_of(c):
    return c if isinstance(c, str) else " ".join(b.get("text", "") for b in c if isinstance(b, dict))

def add(row, dur):
    row[0] += dur; row[1] += 1; row[2] = max(row[2], dur)

# Waiting on CI, agents or the user, not doing work.
WAITING = re.compile(r"watch\.sh|wait loop|AskUserQuestion|wait for CI|gh pr checks|herdr agent wait")

def sessions(pdir, since):
    tools, model, per = defaultdict(lambda: [0.0, 0, 0.0]), defaultdict(float), defaultdict(float)
    for f in glob.glob(os.path.join(pdir, "*.jsonl")):
        if datetime.fromtimestamp(os.path.getmtime(f), timezone.utc) < since:
            continue
        recs = []
        for line in open(f):
            try:
                d = json.loads(line)
            except ValueError:
                continue
            if "timestamp" in d and d.get("type") in ("user", "assistant") and not d.get("isSidechain"):
                recs.append(d)
            elif d.get("type") == "queue-operation" and d.get("operation") == "enqueue":  # task-notifications
                recs.append({"type": "notify", "timestamp": d["timestamp"], "message": {"content": d.get("content", "")}})
        recs = [d for d in recs if ts(d["timestamp"]) >= since]
        if not recs:
            continue
        first = next((text_of(d["message"].get("content", "")) for d in recs if d["type"] == "user"), "")
        who = label(first, os.path.basename(f))
        uses, bg, prev = {}, {}, None
        for d in recs:
            t, c = ts(d["timestamp"]), d["message"].get("content", "")
            if d["type"] == "assistant":
                if prev and prev[0] == "tool":  # model time after a tool result
                    model[who] += (t - prev[1]).total_seconds()
                for b in c if isinstance(c, list) else []:
                    if b.get("type") == "tool_use":
                        uses[b["id"]] = (t, key(b["name"], b.get("input", {})), b.get("input", {}).get("run_in_background"))
                prev = ("asst", t)
                continue
            for m in re.finditer(r"<tool-use-id>(\w+)</tool-use-id>", text_of(c)):
                if m.group(1) in bg:
                    s, k = bg.pop(m.group(1))
                    add(tools[(who, k + " (bg)")], (t - s).total_seconds())
            if d["type"] == "notify":
                continue
            is_tool = False
            for b in c if isinstance(c, list) else []:
                if b.get("type") == "tool_result" and b.get("tool_use_id") in uses:
                    is_tool = True
                    s, k, background = uses.pop(b["tool_use_id"])
                    if background:
                        bg[b["tool_use_id"]] = (s, k)
                        continue
                    dur = (t - s).total_seconds()
                    add(tools[(who, k)], dur); per[who] += dur
            prev = ("tool", t) if is_tool else ("human", t)
    return tools, model, per

def ci(since):
    q = ('.[]|select(.createdAt >= "%s")|.databaseId' % since.strftime("%Y-%m-%dT%H:%M:%SZ"))
    ids = subprocess.run(["gh", "run", "list", "--limit", "100", "--json", "databaseId,createdAt", "--jq", q],
                         capture_output=True, text=True).stdout.split()
    jobs, steps = defaultdict(lambda: [0.0, 0, 0.0]), defaultdict(float)
    for i in ids:
        out = subprocess.run(["gh", "run", "view", i, "--json", "jobs"], capture_output=True, text=True).stdout
        for j in json.loads(out or '{"jobs":[]}')["jobs"]:
            if not j.get("completedAt") or j["completedAt"].startswith("0001"):
                continue
            d = (ts(j["completedAt"]) - ts(j["startedAt"])).total_seconds()
            if j.get("conclusion") == "skipped" or d < 0:
                continue
            add(jobs[j["name"]], d)
            for s in j.get("steps", []):
                if s.get("completedAt") and not s["completedAt"].startswith("0001"):
                    steps[f'{j["name"]} › {s["name"]}'] += (ts(s["completedAt"]) - ts(s["startedAt"])).total_seconds()
    return len(ids), jobs, steps

def fmt(s):
    return f"{s / 60:6.1f}m"

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--since", help="ISO time (local if no zone); default 24 h ago")
    ap.add_argument("--project-dir", default=os.path.expanduser("~/.claude/projects/" + re.sub(r"[^A-Za-z0-9]", "-", os.getcwd())))
    ap.add_argument("--top", type=int, default=15)
    ap.add_argument("--no-ci", action="store_true")
    a = ap.parse_args()
    since = datetime.now(timezone.utc) - timedelta(hours=24)
    if a.since:
        since = datetime.fromisoformat(a.since)
        since = since.astimezone(timezone.utc) if since.tzinfo else since.astimezone().astimezone(timezone.utc)
    tools, model, per = sessions(a.project_dir, since)
    print(f"# Time report since {since.astimezone():%Y-%m-%d %H:%M}\n\n## Sessions (foreground tool time · model time)")
    for who in sorted(set(per) | set(model), key=lambda w: -(per[w] + model[w])):
        print(f"{fmt(per[who])} tools · {fmt(model[who])} model   {who}")
    agg = defaultdict(lambda: [0.0, 0, 0.0])
    for (who, k), (t, n, mx) in tools.items():
        r = agg[k]; r[0] += t; r[1] += n; r[2] = max(r[2], mx)
    for title, waiting in (("Work", False), ("Waiting (CI, agents, user)", True)):
        print(f"\n## {title}: tool time, all sessions (total · calls · max)")
        rows = [x for x in agg.items() if bool(WAITING.search(x[0])) == waiting]
        for k, (t, n, mx) in sorted(rows, key=lambda x: -x[1][0])[: a.top]:
            print(f"{fmt(t)} {n:4d}× max {fmt(mx)}   {k}")
    if not a.no_ci:
        n, jobs, steps = ci(since)
        print(f"\n## CI: {n} runs (total · runs · max)")
        for k, (t, c, mx) in sorted(jobs.items(), key=lambda x: -x[1][0]):
            print(f"{fmt(t)} {c:4d}× max {fmt(mx)}   {k}")
        print("\n## CI: top steps (total)")
        for k, t in sorted(steps.items(), key=lambda x: -x[1])[: a.top]:
            print(f"{fmt(t)}   {k}")

if __name__ == "__main__":
    sys.exit(main())
