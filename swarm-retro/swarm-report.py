#!/usr/bin/env python3
"""Evidence for a swarm retro, read from the swarm db: who did what, where time and attention went.

  swarm-report.py [--db PATH] [--since 2026-11-07T08:00] [--json]

Default db: <git-common-dir>/swarm/swarm.db (or $SWARM_DB). Sections: agents, tasks
(claim -> done time, evidence), event counts per agent (overlaps, reaps, compactions, pushes,
ci-red are the friction signals), messages, locks. Read-only.
"""
import argparse, glob, json, os, re, sqlite3, subprocess, sys
from collections import Counter
from datetime import datetime, timezone

FRICTION = ("overlap", "reap", "compact", "ci-red", "blocked", "push")

def dbpath(a):
    if a:
        return a
    if os.environ.get("SWARM_DB"):
        return os.environ["SWARM_DB"]
    r = subprocess.run(["git", "rev-parse", "--path-format=absolute", "--git-common-dir"], capture_output=True, text=True)
    if r.returncode:
        sys.exit("swarm-report: not in a git repo; pass --db")
    return os.path.join(r.stdout.strip(), "swarm", "swarm.db")

def span(s):
    s = int(s or 0)
    return f"{s // 3600}h{s % 3600 // 60:02d}m" if s >= 3600 else f"{s // 60}m{s % 60:02d}s"

def transcripts(name, cwd):
    if not cwd:
        return []
    d = os.path.expanduser("~/.claude/projects/" + re.sub(r"[^A-Za-z0-9]", "-", cwd))
    rx = re.compile(r"^" + re.escape(name) + r"(-\d+)?$")
    hit = []
    for f in glob.glob(d + "/*.jsonl"):
        with open(f) as fh:
            for _, line in zip(range(40), fh):  # the record sits near the top
                m = re.search(r'"type":"agent-name","agentName":"([^"]+)"', line)
                if m:
                    if rx.match(m[1]):
                        hit.append(f)
                    break
    return sorted(hit, key=os.path.getmtime)

def sh(*cmd):
    r = subprocess.run(cmd, capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else ""

def git_evidence(since=0, ref="origin/main"):
    """Landed commits per agent-hour and files two or more agents changed, from Swarm-Agent trailers."""
    hours, files, commits = {}, {}, []
    for blk in sh("git", "log", ref, *([f"--since={since}"] if since else []), "--name-only", "--format=@@%H\t%ct\t%(trailers:key=Swarm-Agent,valueonly,separator=)").split("@@")[1:]:
        head, *fs = blk.strip().split("\n")
        sha, ct, agent = (head.split("\t") + ["", ""])[:3]
        agent = agent.strip() or "(none)"
        commits.append((int(ct), sha, agent))
        k = (datetime.fromtimestamp(int(ct)).strftime("%Y-%m-%d %H:00"), agent)
        hours[k] = hours.get(k, 0) + 1
        for f in filter(None, fs):
            files.setdefault(f, set()).add(agent)
    return {"commits_per_hour": [{"hour": h, "agent": a, "n": n} for (h, a), n in sorted(hours.items()) if a != "(none)"],
            "not_swarm_commits": sum(n for (h, a), n in hours.items() if a == "(none)"),
            "multi_agent_files": {f: sorted(a) for f, a in files.items() if len(a - {"(none)"}) > 1}, "_commits": commits}

def red_runs(commits, since=0):
    """Failed main runs and the agent whose later green run's commit fixed it (needs gh)."""
    runs = json.loads(sh("gh", "run", "list", "--branch", "main", "--limit", "100", "--json", "conclusion,headSha,createdAt,databaseId") or "[]")
    by = {sha: a for _, sha, a in commits}
    runs = [r for r in runs if r["createdAt"] >= datetime.fromtimestamp(since, timezone.utc).strftime("%Y-%m-%dT%H:%M:%S")]
    runs.sort(key=lambda r: r["createdAt"])
    out = []
    for i, r in enumerate(runs):
        if r["conclusion"] == "failure":
            fix = next((x for x in runs[i + 1:] if x["conclusion"] == "success"), None)
            out.append({"run": r["databaseId"], "broke": by.get(r["headSha"], "?"), "fixed_by": by.get(fix["headSha"], "?") if fix else None})
    return out

def report(c, since=None, git=True):
    if since is None:  # default window: the swarm's start
        since = c.execute("select coalesce(min(started),0) from agent").fetchone()[0]
    q = lambda sql, *p: [dict(r) for r in c.execute(sql, p)]
    ev = q("select * from event where ts>=? order by ts", since)
    out = {"since": since, "agents": q("select name,model,cwd,started,ended,ctx_tokens,status from agent where coalesce(started,0)>=? or ended is null", since)}
    claims = {}
    for e in ev:
        n = (e["data"] or "").split(" ", 1)[0]
        if e["kind"] == "claim":
            claims[n] = e
    tasks = []
    for t in q("select id,title,state,owner,evidence from task"):
        cl = claims.get(f"#{t['id']}")
        done = next((e for e in ev if e["kind"] == "done" and (e["data"] or "").startswith(f"#{t['id']} ")), None)
        t["took"] = span(done["ts"] - cl["ts"]) if cl and done else None
        tasks.append(t)
    out["tasks"] = tasks
    out["events"] = {a: dict(Counter(e["kind"] for e in ev if e["agent"] == a)) for a in sorted({e["agent"] for e in ev})}
    # transcripts: files whose agent-name record is this agent or a relaunched successor (name-2)
    for a in out["agents"]:
        a["transcripts"] = transcripts(a["name"], a.get("cwd"))
        n = a["name"]
        a["msgs_sent"] = c.execute("select count(*) from msg where frm=? and ts>=?", (n, since)).fetchone()[0]
        a["msgs_to_all"] = c.execute("select count(*) from msg where frm=? and dest='@all' and ts>=?", (n, since)).fetchone()[0]
        a["msgs_recv"] = c.execute("select count(*) from msg where (dest=? or dest='@all') and frm!=? and coalesce(kind,'')!='system' and ts>=?", (n, n, since)).fetchone()[0]
        a["tasks_done_no_evidence"] = c.execute("select count(*) from task where owner=? and state='done' and coalesce(evidence,'')=''", (n,)).fetchone()[0]
    out["friction"] = [{k: e[k] for k in ("ts", "agent", "kind", "path", "data")} for e in ev if e["kind"] in FRICTION and e["kind"] != "push"]
    out["overlaps"] = [{k: e[k] for k in ("ts", "agent", "path", "data")} for e in ev if e["kind"] == "overlap"]
    out["idle_with_open_tasks"] = [{"ts": e["ts"], "agent": e["agent"]} for e in ev if e["kind"] == "digest"]
    if git:
        g = git_evidence(since)
        out["red_main_runs"] = red_runs(g.pop("_commits"), since)
        out.update(g)
    out["messages"] = q("select frm, count(*) n, sum(urgent) urgent from msg where ts>=? group by frm", since)
    out["locks"] = q("select path,agent,reason from lock")
    return out

def show(r):
    t = lambda s: datetime.fromtimestamp(s).strftime("%H:%M") if s else "-"
    print("## agents")
    for a in r["agents"]:
        print(f"- {a['name']} {a['model'] or '?'} {t(a['started'])}-{t(a['ended'])} {a['status']} ctx={(a['ctx_tokens'] or 0) // 1000}k msgs sent/recv={a['msgs_sent']}/{a['msgs_recv']} (@all {a['msgs_to_all']}) done-without-evidence={a['tasks_done_no_evidence']}")
        for f in a["transcripts"]:
            print(f"    transcript: {f}")
    print("\n## tasks")
    for k in r["tasks"]:
        print(f"- #{k['id']} {k['state']} {k['owner'] or '-'} {k['took'] or '-'}: {k['title']}" + (f"\n    evidence: {k['evidence']}" if k["evidence"] else ""))
    print("\n## events per agent")
    for a, e in r["events"].items():
        print(f"- {a}: " + ", ".join(f"{k}={v}" for k, v in sorted(e.items())))
    print("\n## friction")
    for e in r["friction"]:
        print(f"- {t(e['ts'])} {e['agent']} {e['kind']} {e['path'] or ''} {e['data'] or ''}".rstrip())
    for key, title in (("commits_per_hour", "landed commits per hour"), ("red_main_runs", "red main runs"),
                       ("overlaps", "overlap events"), ("idle_with_open_tasks", "watchd digests (idle with open tasks)")):
        print(f"\n## {title}")
        for x in r.get(key, []):
            print("- " + " ".join(f"{k}={v}" for k, v in x.items()))
        if key == "commits_per_hour":
            print(f"- not swarm: {r.get('not_swarm_commits', 0)}")
    print("\n## files changed by 2+ agents")
    for f, a in r.get("multi_agent_files", {}).items():
        print(f"- {f}: {', '.join(a)}")
    print("\n## messages sent")
    for m in r["messages"]:
        print(f"- {m['frm']}: {m['n']} ({m['urgent'] or 0} urgent)")
    if r["locks"]:
        print("\n## locks still held")
        for k in r["locks"]:
            print(f"- {k['path']} {k['agent']} {k['reason'] or ''}")

def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--db"); p.add_argument("--since"); p.add_argument("--json", action="store_true")
    a = p.parse_args()
    path = dbpath(a.db)
    if not os.path.exists(path):
        sys.exit(f"swarm-report: no db at {path}")
    c = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
    c.row_factory = sqlite3.Row
    r = report(c, int(datetime.fromisoformat(a.since).timestamp()) if a.since else None)
    print(json.dumps(r, indent=1)) if a.json else show(r)

if __name__ == "__main__":
    main()
