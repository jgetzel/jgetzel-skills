#!/usr/bin/env python3
"""Render a Claude Code transcript (.jsonl) as compact Markdown, for reading or blind judging.

  transcript.py FILE.jsonl [--redact OLD=NEW]... [--last]

--last prints only the final assistant text (probe.sh checks it for PROBE DONE).
"""
import argparse, json, re
from datetime import datetime


def clip(s, n):
    s = re.sub(r"<system-reminder>.*?</system-reminder>", "", s, flags=re.S).strip()
    return s if len(s) <= n else s[:n] + f" …[{len(s) - n} more chars]"


def text_of(c):
    return c if isinstance(c, str) else "\n".join(b.get("text", "") for b in c if isinstance(b, dict) and b.get("type") == "text")


def summary(inp):
    for k in ("command", "file_path", "pattern", "skill", "url", "query", "description"):
        if inp.get(k):
            return str(inp[k])
    return json.dumps(inp)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("--redact", action="append", default=[])
    ap.add_argument("--last", action="store_true")
    a = ap.parse_args()
    recs = []
    for line in open(a.file):
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if d.get("type") in ("user", "assistant") and not d.get("isSidechain"):
            recs.append(d)
    if a.last:
        texts = [text_of(d["message"]["content"]) for d in recs if d["type"] == "assistant"]
        print(next((t for t in reversed(texts) if t.strip()), ""))
        return
    out, calls, errors = [], 0, 0
    for d in recs:
        c = d["message"].get("content", "")
        if d["type"] == "user" and isinstance(c, str):
            meta = d.get("isMeta")  # skill bodies, injected context, cross-session messages
            out.append(f"\n### user{' (meta)' if meta else ''}\n{clip(c, 600 if meta else 3000)}\n")
            continue
        for b in c if isinstance(c, list) else []:
            t = b.get("type")
            if t == "text" and b["text"].strip():
                out.append(f"\n**{d['type']}:** {clip(b['text'], 3000)}\n")
            elif t == "tool_use":
                calls += 1
                out.append(f"→ {b['name']}: {clip(summary(b.get('input', {})), 400)}")
            elif t == "tool_result":
                body = b.get("content")
                body = text_of(body) if isinstance(body, list) else str(body or "")
                errors += bool(b.get("is_error"))
                out.append(f"  ← {'ERROR ' if b.get('is_error') else ''}{clip(body, 400)}".replace("\n", "\n    "))
    ts = [datetime.fromisoformat(d["timestamp"].replace("Z", "+00:00")) for d in recs if "timestamp" in d]
    mins = (ts[-1] - ts[0]).total_seconds() / 60 if ts else 0
    text = f"# Transcript: {mins:.0f} min, {calls} tool calls, {errors} errors\n" + "\n".join(out)
    for r in a.redact:
        old, new = r.split("=", 1)
        text = text.replace(old, new)
    print(text)


if __name__ == "__main__":
    main()
