#!/usr/bin/env python3
"""Evidence for a swarm retro, read from the swarm db: who did what, where time and attention went.

  swarm-report.py [--db PATH] [--since 2026-11-07T08:00] [--json]

Default db: <git-common-dir>/swarm/swarm.db (or $SWARM_DB). Sections: agents, tasks
(claim -> done time, evidence), event counts per agent (overlaps, reaps, compactions, pushes,
ci-red are the friction signals), messages, locks. Read-only.
"""
import argparse, glob, json, os, re, sqlite3, subprocess, sys
from collections import Counter
from datetime import datetime

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

def report(c, since=0):
    q = lambda sql, *p: [dict(r) for r in c.execute(sql, p)]
    ev = q("select * from event where ts>=? order by ts", since)
    out = {"agents": q("select name,model,cwd,started,ended,ctx_tokens,status from agent where coalesce(started,0)>=? or ended is null", since)}
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
    # transcripts: Claude Code keeps one dir per cwd; match sessions by mtime inside the run window
    for a in out["agents"]:
        d = os.path.expanduser("~/.claude/projects/" + re.sub(r"[^A-Za-z0-9]", "-", a.get("cwd") or ""))
        a["transcripts"] = sorted(glob.glob(d + "/*.jsonl"), key=os.path.getmtime)[-3:] if a.get("cwd") else []
        n = a["name"]
        a["msgs_sent"] = c.execute("select count(*) from msg where frm=? and ts>=?", (n, since)).fetchone()[0]
        a["msgs_to_all"] = c.execute("select count(*) from msg where frm=? and dest='@all' and ts>=?", (n, since)).fetchone()[0]
        a["msgs_recv"] = c.execute("select count(*) from msg where (dest=? or dest='@all') and frm!=? and ts>=?", (n, n, since)).fetchone()[0]
        a["tasks_done_no_evidence"] = c.execute("select count(*) from task where owner=? and state='done' and coalesce(evidence,'')=''", (n,)).fetchone()[0]
    out["friction"] = [{k: e[k] for k in ("ts", "agent", "kind", "path", "data")} for e in ev if e["kind"] in FRICTION and e["kind"] != "push"]
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
    r = report(c, int(datetime.fromisoformat(a.since).timestamp()) if a.since else 0)
    print(json.dumps(r, indent=1)) if a.json else show(r)

if __name__ == "__main__":
    main()
