#!/usr/bin/env python3
"""Check the harness mechanically and count what every session pays for.

  harness-lint.py [--repo DIR] [--max-bytes N]

Always-on bytes: user and project CLAUDE.md (+ @imports), .claude/rules, the auto-memory
MEMORY.md (first 200 lines). Errors (exit 1): a skill without SKILL.md or description, a
name that doesn't match its directory, a referenced skill script that is missing or not
executable, settings that don't parse, a hook command path that doesn't exist, a hook or
skill script that doesn't compile, always-on bytes over --max-bytes.
"""
import argparse, glob, json, os, re, subprocess

HOME = os.path.expanduser("~")
EVENTS = {"PreToolUse", "PostToolUse", "PostToolUseFailure", "PermissionRequest", "PermissionDenied", "Notification",
          "UserPromptSubmit", "Stop", "StopFailure", "SubagentStart", "SubagentStop", "PreCompact", "PostCompact",
          "SessionStart", "SessionEnd", "Setup", "TeammateIdle", "TaskCreated", "TaskCompleted", "ConfigChange",
          "CwdChanged", "FileChanged", "InstructionsLoaded", "WorktreeCreate", "WorktreeRemove", "Elicitation",
          "ElicitationResult"}
errors, warnings = [], []


def imports(path, seen):
    """A CLAUDE.md and the files it @imports, recursively (max depth 5, like Claude Code)."""
    if path in seen or len(seen) > 50 or not os.path.isfile(path):
        return
    seen.append(path)
    text = re.sub(r"```.*?```|`[^`\n]*`", "", open(path, errors="replace").read(), flags=re.S)
    for m in re.finditer(r"(?:^|\s)@((?:~|\.{1,2})?/?[\w./-]+)", text):
        p = os.path.normpath(os.path.join(os.path.dirname(path), os.path.expanduser(m.group(1))))
        if os.path.isfile(p):
            imports(p, seen)
        elif "/" in m.group(1):
            warnings.append(f"{path}: @{m.group(1)} not found")


def always_on(repo):
    files = []
    for f in [f"{HOME}/.claude/CLAUDE.md"] + ([f"{repo}/CLAUDE.md", f"{repo}/CLAUDE.local.md", f"{repo}/.claude/CLAUDE.md"] if repo else []):
        imports(f, files)
    if repo:
        files += sorted(glob.glob(f"{repo}/.claude/rules/**/*.md", recursive=True))
        common = subprocess.run(["git", "-C", repo, "rev-parse", "--path-format=absolute", "--git-common-dir"],
                                capture_output=True, text=True).stdout.strip()
        root = os.path.dirname(common) if common.endswith("/.git") else repo
        mem = f"{HOME}/.claude/projects/{re.sub(r'[^A-Za-z0-9]', '-', root)}/memory/MEMORY.md"
        if os.path.isfile(mem):
            files.append(mem)
    rows = []
    for f in files:
        data = open(f, "rb").read()
        if f.endswith("/memory/MEMORY.md"):
            data = b"\n".join(data.split(b"\n")[:200])
        rows.append((len(data), f))
    return rows


def compiles(path):
    if path.endswith(".py"):
        try:
            compile(open(path, encoding="utf-8").read(), path, "exec")
        except (SyntaxError, ValueError) as e:
            errors.append(f"{path}: does not compile: {e}")
    elif path.endswith(".sh"):
        r = subprocess.run(["bash", "-n", path], capture_output=True, text=True)
        if r.returncode:
            errors.append(f"{path}: bash -n: {r.stderr.strip()}")


def skills(repo):
    dirs = sorted(glob.glob(f"{HOME}/.claude/skills/*/")) + (sorted(glob.glob(f"{repo}/.claude/skills/*/")) if repo else [])
    for d in dirs:
        d, name = d.rstrip("/"), os.path.basename(d.rstrip("/"))
        md = f"{d}/SKILL.md"
        if not os.path.isfile(md):
            if not glob.glob(f"{d}/**/SKILL.md", recursive=True):  # a container of skills, e.g. a synced bundle
                errors.append(f"{d}: no SKILL.md")
            continue
        text = open(md, errors="replace").read()
        fm = re.match(r"---\n(.*?)\n---", text, re.S)
        meta = dict(re.findall(r"^(\w[\w-]*):\s*(.*)$", fm.group(1), re.M)) if fm else {}
        desc = meta.get("description", "").strip().strip("\"'")
        if not desc:
            errors.append(f"{md}: no description in frontmatter (the skill never triggers)")
        elif len(desc) > 1024:
            warnings.append(f"{md}: description is {len(desc)} chars (limit 1024)")
        if meta.get("name") and meta["name"].strip() != name:
            errors.append(f"{md}: name '{meta['name'].strip()}' does not match directory '{name}'")
        for m in re.finditer(r"(\b(?:python3?|bash|sh)\s+)?(~/\.claude/skills/[\w./-]+\.(?:sh|py))", text):
            p = os.path.expanduser(m.group(2))
            if not os.path.isfile(p):
                errors.append(f"{md}: references {m.group(2)}, which does not exist")
            elif not m.group(1) and not os.access(p, os.X_OK):
                errors.append(f"{md}: runs {m.group(2)} directly but it is not executable")
        for f in glob.glob(f"{d}/**/*.py", recursive=True) + glob.glob(f"{d}/**/*.sh", recursive=True):
            compiles(f)


def settings(repo):
    files = [f"{HOME}/.claude/settings.json", f"{HOME}/.claude/settings.local.json"]
    files += [f"{repo}/.claude/settings.json", f"{repo}/.claude/settings.local.json"] if repo else []
    for f in filter(os.path.isfile, files):
        try:
            hooks = json.load(open(f)).get("hooks", {})
        except ValueError as e:
            errors.append(f"{f}: invalid JSON: {e}")
            continue
        for event, entries in hooks.items():
            if event not in EVENTS:
                warnings.append(f"{f}: unknown hook event {event}")
            for h in (h for e in entries for h in e.get("hooks", [])):
                for tok in re.findall(r"""(?:^|(?<=[\s"'=(]))((?:~|\$HOME|\$\{HOME\}|\$CLAUDE_PROJECT_DIR|/)[^\s"';|&]*)""", h.get("command", "")):
                    if not re.search(r"\.(py|sh)$|/bin/", tok):
                        continue
                    p = os.path.expanduser(tok.replace("$CLAUDE_PROJECT_DIR", repo or "").replace("${HOME}", HOME).replace("$HOME", HOME))
                    if not os.path.exists(p):
                        errors.append(f"{f}: {event} hook runs {tok}, which does not exist")
                    else:
                        compiles(p)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", help="default: the cwd's git root")
    ap.add_argument("--max-bytes", type=int)
    a = ap.parse_args()
    repo = a.repo or subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True).stdout.strip()
    rows = always_on(repo)
    total = sum(n for n, _ in rows)
    print("## Always-on bytes")
    for n, f in rows:
        print(f"{n:7d}  {f.replace(HOME, '~')}")
    print(f"{total:7d}  total")
    if a.max_bytes and total > a.max_bytes:
        errors.append(f"always-on is {total} bytes, over --max-bytes {a.max_bytes}")
    skills(repo)
    settings(repo)
    for w in warnings:
        print(f"warn: {w}")
    for e in errors:
        print(f"ERROR: {e}")
    print("ok" if not errors else f"{len(errors)} error(s)")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
